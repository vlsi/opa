// Copyright 2026 The OPA Authors.  All rights reserved.
// Use of this source code is governed by an Apache2
// license that can be found in the LICENSE file.

package rego

import (
	"fmt"
	"strings"
	"testing"

	"github.com/open-policy-agent/opa/v1/ast"
)

// BenchmarkIndexedInputMembershipEval evaluates rules that grant access when
// the input names a resource and carries the permission for it:
//
//	"p17" in input.perms
//	input.id == "r17"
//
// The index narrows the rules to the one resource either way, so the number of
// expressions evaluated does not depend on how many permissions the input
// carries. The time spent looking the rules up in the index may.
//
// The dimensions are:
//
//   - rules: 100 clauses in one rule, or 2500 split into rules of 100 clauses
//     each, called from one entry rule; every piece has an index of its own,
//     and each is looked up in turn;
//   - order: whether the membership test or the equality comes first in each
//     clause;
//   - input: perms as an array, as a set, or as an object of true values read
//     with input.perms["p17"], which the index sees as an equality;
//   - held: whether the permissions the input carries are ones no rule needs,
//     or permissions of other resources, "p0", "p1", and so on;
//   - perms: how many permissions the input carries.
//
// The resource asked for exists, and the permission it needs is not among
// those the input carries, so every lookup ends in a denial.
func BenchmarkIndexedInputMembershipEval(b *testing.B) {
	ctx := b.Context()

	for _, shape := range []struct{ rules, chunk int }{{100, 0}, {2500, 100}} {
		for _, order := range []string{"in-first", "eq-first"} {
			for _, form := range []string{"array", "set", "object"} {
				name := fmt.Sprintf("rules=%d/chunk=%d/order=%s/input=%s", shape.rules, shape.chunk, order, form)
				b.Run(name, func(b *testing.B) {
					module := membershipRuleset(shape.rules, shape.chunk, order == "in-first", form == "object")
					pq, err := New(
						ParsedQuery(ast.MustParseBody("data.test.allow")),
						ParsedModule(ast.MustParseModule(module)),
					).PrepareForEval(ctx)
					if err != nil {
						b.Fatal(err)
					}

					for _, held := range []string{"none", "others"} {
						for _, perms := range []int{2, 1000} {
							b.Run(fmt.Sprintf("held=%s/perms=%d", held, perms), func(b *testing.B) {
								input := membershipInput(form, shape.rules-1, perms, held == "others")
								rs, err := pq.Eval(ctx, EvalParsedInput(input))
								if err != nil {
									b.Fatal(err)
								}
								if len(rs) != 1 || rs[0].Expressions[0].Value != false {
									b.Fatalf("expected allow = false, got %v", rs)
								}

								b.ReportAllocs()
								b.ResetTimer()
								for b.Loop() {
									if _, err := pq.Eval(ctx, EvalParsedInput(input)); err != nil {
										b.Fatal(err)
									}
								}
							})
						}
					}
				})
			}
		}
	}
}

// membershipRuleset returns a module granting access to resource rK on
// permission pK, for K below rules. A chunk of 0 puts every clause in allow; a
// positive chunk splits the clauses into rules of that many clauses each.
func membershipRuleset(rules, chunk int, inFirst, object bool) string {
	var sb strings.Builder
	sb.WriteString("package test\n\ndefault allow := false\n\n")

	body := func(k int) string {
		check := fmt.Sprintf("\"p%d\" in input.perms", k)
		if object {
			check = fmt.Sprintf("input.perms[\"p%d\"]", k)
		}
		eq := fmt.Sprintf("input.id == \"r%d\"", k)
		if inFirst {
			return "\t" + check + "\n\t" + eq + "\n"
		}
		return "\t" + eq + "\n\t" + check + "\n"
	}

	if chunk == 0 {
		for k := range rules {
			fmt.Fprintf(&sb, "allow if {\n\tinput.type == \"t\"\n\tinput.op == \"o\"\n%s}\n\n", body(k))
		}
		return sb.String()
	}

	for c := 0; c*chunk < rules; c++ {
		fmt.Fprintf(&sb, "allow if {\n\tinput.type == \"t\"\n\tinput.op == \"o\"\n\ts%d\n}\n\n", c)
		for k := c * chunk; k < min(rules, (c+1)*chunk); k++ {
			fmt.Fprintf(&sb, "s%d if {\n%s}\n\n", c, body(k))
		}
	}
	return sb.String()
}

// membershipInput asks for resource rK with perms permissions, none of which is
// pK: "p0", "p1", and so on, skipping pK, when others is set, and "q0", "q1",
// and so on otherwise.
func membershipInput(form string, k, perms int, others bool) ast.Value {
	terms := make([]*ast.Term, 0, perms)
	for j := 0; len(terms) < perms; j++ {
		switch {
		case !others:
			terms = append(terms, ast.StringTerm(fmt.Sprintf("q%d", j)))
		case j != k:
			terms = append(terms, ast.StringTerm(fmt.Sprintf("p%d", j)))
		}
	}

	var ps *ast.Term
	switch form {
	case "array":
		ps = ast.ArrayTerm(terms...)
	case "set":
		ps = ast.SetTerm(terms...)
	case "object":
		kvs := make([][2]*ast.Term, perms)
		for j, t := range terms {
			kvs[j] = [2]*ast.Term{t, ast.BooleanTerm(true)}
		}
		ps = ast.ObjectTerm(kvs...)
	}

	return ast.NewObject(
		[2]*ast.Term{ast.StringTerm("type"), ast.StringTerm("t")},
		[2]*ast.Term{ast.StringTerm("op"), ast.StringTerm("o")},
		[2]*ast.Term{ast.StringTerm("id"), ast.StringTerm(fmt.Sprintf("r%d", k))},
		[2]*ast.Term{ast.StringTerm("perms"), ps},
	)
}

// BenchmarkIndexedSharedRoleEval evaluates 150 rules that all require one role
// from input.roles and each constrain one of three fields to a value of its
// own. The role check is the most frequent ref, so the index tests it once, at
// the top; ranking membership below equality regardless of frequency would have
// every field level lead to a role level of its own, each walking input.roles.
func BenchmarkIndexedSharedRoleEval(b *testing.B) {
	ctx := b.Context()

	var sb strings.Builder
	sb.WriteString("package test\n\ndefault allow := false\n\n")
	for _, field := range []string{"x", "y", "z"} {
		for k := range 50 {
			fmt.Fprintf(&sb, "allow if {\n\t\"admin\" in input.roles\n\tinput.%s == \"v%d\"\n}\n\n", field, k)
		}
	}

	pq, err := New(
		ParsedQuery(ast.MustParseBody("data.test.allow")),
		ParsedModule(ast.MustParseModule(sb.String())),
	).PrepareForEval(ctx)
	if err != nil {
		b.Fatal(err)
	}

	for _, roles := range []int{2, 1000} {
		b.Run(fmt.Sprintf("roles=%d", roles), func(b *testing.B) {
			terms := make([]*ast.Term, roles)
			for j := range roles {
				terms[j] = ast.StringTerm(fmt.Sprintf("q%d", j))
			}
			input := ast.NewObject(
				[2]*ast.Term{ast.StringTerm("x"), ast.StringTerm("v1")},
				[2]*ast.Term{ast.StringTerm("y"), ast.StringTerm("v2")},
				[2]*ast.Term{ast.StringTerm("z"), ast.StringTerm("v3")},
				[2]*ast.Term{ast.StringTerm("roles"), ast.ArrayTerm(terms...)},
			)

			b.ReportAllocs()
			for b.Loop() {
				if _, err := pq.Eval(ctx, EvalParsedInput(input)); err != nil {
					b.Fatal(err)
				}
			}
		})
	}
}

// BenchmarkIndexedMembershipTieEval evaluates rules where input.roles and
// input.x are each constrained by 100 rules: 50 require a role and x = "v1", 50
// only a role, and 50 only a value of x. With input.x ahead of input.roles, a
// lookup for x = "v1" reaches the role level twice, through the child for "v1"
// and through the rules that leave x open; with input.roles ahead, once.
func BenchmarkIndexedMembershipTieEval(b *testing.B) {
	ctx := b.Context()

	var sb strings.Builder
	sb.WriteString("package test\n\ndefault allow := false\n\n")
	for k := range 50 {
		fmt.Fprintf(&sb, "allow if {\n\t\"r%d\" in input.roles\n\tinput.x == \"v1\"\n}\n\n", k)
		fmt.Fprintf(&sb, "allow if {\n\t\"r%d\" in input.roles\n}\n\n", k)
		fmt.Fprintf(&sb, "allow if {\n\tinput.x == \"v%d\"\n}\n\n", k+100)
	}

	pq, err := New(
		ParsedQuery(ast.MustParseBody("data.test.allow")),
		ParsedModule(ast.MustParseModule(sb.String())),
	).PrepareForEval(ctx)
	if err != nil {
		b.Fatal(err)
	}

	for _, roles := range []int{2, 1000} {
		b.Run(fmt.Sprintf("roles=%d", roles), func(b *testing.B) {
			terms := make([]*ast.Term, roles)
			for j := range roles {
				terms[j] = ast.StringTerm(fmt.Sprintf("q%d", j))
			}
			input := ast.NewObject(
				[2]*ast.Term{ast.StringTerm("x"), ast.StringTerm("v1")},
				[2]*ast.Term{ast.StringTerm("roles"), ast.ArrayTerm(terms...)},
			)

			b.ReportAllocs()
			for b.Loop() {
				if _, err := pq.Eval(ctx, EvalParsedInput(input)); err != nil {
					b.Fatal(err)
				}
			}
		})
	}
}
