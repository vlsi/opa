// Copyright 2026 The OPA Authors.  All rights reserved.
// Use of this source code is governed by an Apache2
// license that can be found in the LICENSE file.

package rego

import (
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/open-policy-agent/opa/v1/ast"
)

// BenchmarkIndexedPermissionGroupEval evaluates 2000 clauses in one rule where
// several clauses share a resource and differ only in the permission they
// require:
//
//	input.id == "r3"
//	"p17" in input.perms      (or input.perms["p17"])
//
// group is the number of clauses per resource: with 1, input.id narrows the
// candidates to one clause; with 2000, every clause names the same resource and
// only the permission tells them apart. The input asks for resource r0 without
// the permission it needs, so every lookup ends in a denial; see
// permissionGroupInput for the permissions it carries. prepare-ms is the time
// PrepareForEval took for the module.
func BenchmarkIndexedPermissionGroupEval(b *testing.B) {
	ctx := b.Context()
	const clauses = 2000

	for _, group := range []int{1, 10, 100, 2000} {
		for _, form := range []string{"array", "object"} {
			b.Run(fmt.Sprintf("group=%d/input=%s", group, form), func(b *testing.B) {
				module := permissionGroupRuleset(clauses, group, form == "object")
				start := time.Now()
				pq, err := New(
					ParsedQuery(ast.MustParseBody("data.test.allow")),
					ParsedModule(ast.MustParseModule(module)),
				).PrepareForEval(ctx)
				if err != nil {
					b.Fatal(err)
				}
				prepare := time.Since(start)

				for _, perms := range []int{2, 1000} {
					b.Run(fmt.Sprintf("perms=%d", perms), func(b *testing.B) {
						input := permissionGroupInput(form, clauses, group, perms)
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
						b.ReportMetric(float64(prepare.Milliseconds()), "prepare-ms")
					})
				}
			})
		}
	}
}

// permissionGroupRuleset returns a module granting access to resource r(K/group)
// on permission pK, for K below clauses, all in one rule.
func permissionGroupRuleset(clauses, group int, object bool) string {
	var sb strings.Builder
	sb.WriteString("package test\n\ndefault allow := false\n\n")
	for k := range clauses {
		check := fmt.Sprintf("\"p%d\" in input.perms", k)
		if object {
			check = fmt.Sprintf("input.perms[\"p%d\"]", k)
		}
		fmt.Fprintf(&sb, "allow if {\n\tinput.type == \"t\"\n\tinput.id == \"r%d\"\n\t%s\n}\n\n", k/group, check)
	}
	return sb.String()
}

// permissionGroupInput asks for resource r0 with perms permissions. Where the
// resource has fewer clauses than the module, half of them are permissions of
// other resources, from the last clause down; the rest are "x1", "x3", and so
// on, which no clause requires.
func permissionGroupInput(form string, clauses, group, perms int) ast.Value {
	terms := make([]*ast.Term, 0, perms)
	for j := range perms {
		if k := clauses - 1 - j/2; j%2 == 0 && k/group != 0 {
			terms = append(terms, ast.StringTerm(fmt.Sprintf("p%d", k)))
		} else {
			terms = append(terms, ast.StringTerm(fmt.Sprintf("x%d", j)))
		}
	}
	var ps *ast.Term
	if form == "object" {
		kvs := make([][2]*ast.Term, len(terms))
		for j, t := range terms {
			kvs[j] = [2]*ast.Term{t, ast.BooleanTerm(true)}
		}
		ps = ast.ObjectTerm(kvs...)
	} else {
		ps = ast.ArrayTerm(terms...)
	}
	return ast.NewObject(
		[2]*ast.Term{ast.StringTerm("type"), ast.StringTerm("t")},
		[2]*ast.Term{ast.StringTerm("id"), ast.StringTerm("r0")},
		[2]*ast.Term{ast.StringTerm("perms"), ps},
	)
}
