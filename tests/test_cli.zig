//! Integration gates — command-line contract: usage, flags, error diagnostics, and the fmt --check exemplars, plus kernel-mechanic fixtures (define, div guards, not_intro, forward refs, case/shadow rules).
//!
//! Each gate spawns the built `bpa` binary and asserts its stdout / stderr /
//! exit code; wired into the `test` step via `test_step.dependOn`.

const std = @import("std");
const Ctx = @import("Ctx.zig");

pub fn addTests(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    test_step: *std.Build.Step,
) void {
    const ctx = Ctx.init(b, exe, test_step);

    // No arguments -> usage on stderr, exit 1.
    const no_args = b.addRunArtifact(exe);
    no_args.has_side_effects = true;
    no_args.expectStdErrEqual(
        "usage: bpa check [--fast | --faster | --reckless] [--draft] <file.bpa>\n" ++
            "       bpa fmt [--check] <file.bpa|.md>\n" ++
            "       bpa lint <file.bpa|.md>\n" ++
            "       bpa debug accelerant <file> <line | theorem step-label>\n" ++
            "       bpa debug taint <file> [theorem]\n" ++
            "       bpa query outline <file.bpa> [theorem]\n" ++
            "       bpa query theorem <file.bpa> <theorem> [--sig]\n" ++
            "       bpa query whereis <file.bpa> <identifier>\n" ++
            "       bpa query search <file.bpa|dir> <query>\n" ++
            "       bpa query uses <file.bpa> [theorem]\n",
    );
    no_args.expectExitCode(1);
    test_step.dependOn(&no_args.step);

    // fmt --check: the exemplars are canonically formatted. The `.md` entries
    // exercise the literate path (formatLiterate reflows the ```bpa blocks and
    // leaves prose verbatim); the rest are plain `.bpa` sources.
    for ([_][]const u8{ "examples/peano.bpa", "examples/peano-pure.bpa", "examples/peano-imports.bpa", "examples/gauss.bpa", "examples/gauss-pure.bpa", "examples/euclid.bpa", "examples/euclid-compute.bpa", "examples/incorrect.bpa", "examples/sqrt2.bpa", "std/peano.bpa", "std/peano-ordering.bpa", "std/peano-subtraction.bpa", "std/peano-division.bpa", "std/peano-gcd.bpa", "std/peano-parity.bpa", "std/group.bpa", "std/group-power.bpa", "std/ring.bpa", "std/integer-ring-model.bpa", "std/set.bpa", "std/collection.bpa", "std/function.bpa", "std/function-invertible.bpa", "std/integer.bpa", "std/integer-ring.bpa", "std/integer-order.bpa", "std/integer-wellordering.bpa", "std/integer-divides.bpa", "std/integer-division.bpa", "std/divisibility.bpa", "std/integer-nonneg.bpa", "std/element.bpa", "std/relation.bpa", "std/equivalence.bpa", "aata/3.2-groups.md", "aata/1.2.1-sets.md", "aata/1.2.2-functions.md", "aata/1.2.3-relations.md", "aata/1.2.3-partitions.md", "aata/2.1-induction.md", "aata/2.2-division-algorithm.md", "aata/2.3-primes.md", "tests/cases/kebab_label_ok.bpa", "tests/cases/schema_eta.bpa", "tests/cases/schema_binary_param.bpa", "tests/cases/schema_wellformed_ok.bpa", "tests/cases/schema_wellformed_bad.bpa", "tests/cases/choice_description.bpa", "tests/cases/model_accel_simplify.bpa", "tests/cases/model_accel_assoc.bpa", "tests/cases/model_accel_assoc_commut.bpa", "tests/cases/model_accel_tautology.bpa", "tests/cases/model_accel_polynomial.bpa", "tests/cases/model_accel_arithmetic.bpa", "tests/cases/model_accel_ext.bpa", "tests/cases/case_split.bpa", "tests/cases/fix_sibling_reuse.bpa", "tests/cases/outline.bpa", "tests/cases/assoc_commut_custom.bpa", "tests/cases/assoc_commut_bad_arity.bpa", "tests/cases/assoc_commut_oracle.bpa", "tests/cases/polynomial_oracle.bpa", "tests/cases/search_target.bpa", "tests/cases/assoc.bpa", "tests/cases/assoc_bad.bpa", "tests/cases/assoc_missing_arg.bpa", "tests/cases/assoc_oracle.bpa", "tests/cases/axiom_as_step_bad.bpa" }) |path| {
        const fmt_check = b.addRunArtifact(exe);
        fmt_check.has_side_effects = true;
        fmt_check.setCwd(b.path("."));
        fmt_check.addArgs(&.{ "fmt", "--check", path });
        fmt_check.expectStdErrEqual("");
        fmt_check.expectExitCode(0);
        test_step.dependOn(&fmt_check.step);
    }

    // lint: canonical binder order. The fixture's `bad` axiom reverses
    // first-appearance order; lint flags it (exit 1) and leaves `good` alone.
    ctx.fail(
        &.{ "lint", "tests/cases/lint_binder_order.bpa" },
        "tests/cases/lint_binder_order.bpa:11:12: error: non-canonical binder order: 'forall b, a' should be 'forall a, b' (first-appearance order in the body)\n",
    );

    // Nonexistent file -> clean diagnostic on stderr, exit 1.
    ctx.fail(&.{ "check", "nosuchfile.bpa" }, "error: cannot open 'nosuchfile.bpa': file not found\n");

    // Existing, valid file -> parses and checks with no diagnostics. It is
    // comments-only, so it materializes 0 theorems and exits nonzero with
    // the "nothing was checked" warning (valid, but proves nothing).
    const ok = b.addRunArtifact(exe);
    ok.has_side_effects = true;
    ok.addArg("check");
    ok.addFileArg(b.path("tests/cases/smoke.bpa"));
    ok.expectStdErrEqual("");
    ok.expectExitCode(1);
    test_step.dependOn(&ok.step);

    // Syntax error -> exact diagnostic with line:col on stderr, exit 1.
    // cwd pinned to build root so the relative path in the diagnostic is stable.
    ctx.fail(&.{ "check", "tests/cases/syntax_err.bpa" }, "tests/cases/syntax_err.bpa:4:11: error: expected ':', got 'forall'\n");

    // M2: full declaration surface elaborates cleanly. A decls-only file
    // materializes 0 theorems, so it exits nonzero with the "nothing was
    // checked" warning (clean elaboration, but nothing to prove).
    const decls = b.addRunArtifact(exe);
    decls.has_side_effects = true;
    decls.setCwd(b.path("."));
    decls.addArgs(&.{ "check", "tests/cases/pa_decls.bpa" });
    decls.expectStdErrEqual("");
    decls.expectExitCode(1);
    test_step.dependOn(&decls.step);

    // M2: sort errors are caught at elaboration with a precise location.
    ctx.fail(&.{ "check", "tests/cases/sort_mismatch.bpa" }, "tests/cases/sort_mismatch.bpa:5:17: error: expected sort 'Nat', got 'Prop'\n");

    // M3: proofs that must check
    ctx.okSilent(&.{ "check", "tests/cases/modus_ponens.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/imp_chain.bpa" });
    ctx.okSilent(&.{ "check", "tests/cases/forall_swap.bpa" });

    // M3: broken siblings with exact diagnostics
    ctx.fail(&.{ "check", "tests/cases/modus_ponens_bad.bpa" }, "tests/cases/modus_ponens_bad.bpa:16:22: error: modus_ponens expects an implication, got 'p'\n");

    // citing an axiom where a proof STEP is required: the diagnostic must
    // point at the fix (materialize it as a step first), not report a bare
    // "unknown reference".
    ctx.fail(&.{ "check", "tests/cases/axiom_as_step_bad.bpa" }, "tests/cases/axiom_as_step_bad.bpa:14:24: error: 'pall' is an axiom, not a proof step; introduce it as a step first with `[by axiom pall]`, then reference that step\n");

    ctx.fail(&.{ "check", "tests/cases/fix_shadow_bad.bpa" }, "tests/cases/fix_shadow_bad.bpa:10:13: error: 'a' shadows an enclosing variable; choose a fresh name\n");

    // M6: --help
    const help = b.addRunArtifact(exe);
    help.has_side_effects = true;
    help.addArg("--help");
    help.expectExitCode(0);
    test_step.dependOn(&help.step);

    // M4: ill-sorted schema argument dies at the use site
    ctx.fail(&.{ "check", "tests/cases/induction_bad_sort.bpa" }, "tests/cases/induction_bad_sort.bpa:14:46: error: expected a proposition, got sort 'Nat'\n");

    // proof-carrying schema `zeroLike(t): t = ZERO` whose body only survives the
    // t := ZERO instance. STRICT rejects it at DECLARATION (opaque-parameter check:
    // the body must hold generically, and `opaque = ZERO` is not reflexivity) AND
    // at the failing instantiation. An over-general schema is unsound as written;
    // proving one true specialization does not rescue it.
    ctx.fail(&.{ "check", "tests/cases/schema_per_instance.bpa" },
        \\tests/cases/schema_per_instance.bpa:10:4: error: reflexivity requires a claim of the form 't = t', got 'succ(ZERO) = ZERO'
        \\tests/cases/schema_per_instance.bpa:10:4: error: reflexivity requires a claim of the form 't = t', got 'opaque-schema-param#1 = ZERO'
        \\tests/cases/schema_per_instance.bpa:29:21: error: instantiation of schema 'zeroLike' failed here
        \\
    );
    // --fast keeps the lazy per-instance behavior: the schema declares fine (body
    // unchecked), and only the bad instantiation `zeroLike(succ ZERO)` fails.
    ctx.fail(&.{ "check", "--fast", "tests/cases/schema_per_instance.bpa" },
        \\tests/cases/schema_per_instance.bpa:10:4: error: reflexivity requires a claim of the form 't = t', got 'succ(ZERO) = ZERO'
        \\tests/cases/schema_per_instance.bpa:29:21: error: instantiation of schema 'zeroLike' failed here
        \\
    );

    // forward label references: a step may cite a later-defined label
    ctx.ok(&.{ "check", "tests/cases/forward_ref.bpa" }, "OK: 6 declarations, 1 theorems proven\n");

    // mutually-citing steps form a justification cycle, reported by name
    ctx.fail(&.{ "check", "tests/cases/forward_ref_cycle.bpa" }, "tests/cases/forward_ref_cycle.bpa:10:4: error: cyclic justification: a -> b -> a\n");

    // a self-instantiating schema is a named cycle, not a blunt depth cap. The
    // strict declaration-time opaque check catches it first (its body instantiates
    // itself); the later real instantiation site reports it again.
    ctx.fail(&.{ "check", "tests/cases/schema_cycle.bpa" },
        \\tests/cases/schema_cycle.bpa:11:21: error: schema instantiation cycle: loopy -> loopy
        \\tests/cases/schema_cycle.bpa:11:21: error: schema instantiation cycle: loopy -> loopy
        \\tests/cases/schema_cycle.bpa:19:21: error: instantiation of schema 'loopy' failed here
        \\
    );

    // a deep but terminating instantiation chain (10 distinct schemas) is
    // accepted — the old inst_depth cap wrongly rejected it
    ctx.ok(&.{ "check", "tests/cases/schema_deep_ok.bpa" }, "OK: 12 declarations, 1 theorems proven\n");

    // kebab-case is rejected in a declaration-name position (parser)
    ctx.fail(&.{ "check", "tests/cases/kebab_decl_bad.bpa" }, "tests/cases/kebab_decl_bad.bpa:6:6: error: expected 'identifier', got 'foo-bar'\n");

    // kebab-case IS allowed for proof labels and [by ...] references
    ctx.ok(&.{ "check", "tests/cases/kebab_label_ok.bpa" }, "OK: 4 declarations, 1 theorems proven\n");

    // eta-sugar: a schema Nat->Prop param accepts a bare predicate name
    ctx.ok(&.{ "check", "tests/cases/schema_eta.bpa" }, "OK: 8 declarations, 1 theorems proven\n");

    // N-ary schema params: a RELATIONAL (2-arg) `Element -> Element -> Prop` param,
    // instantiated by a bare binary predicate (eta) and a 2-binder lambda, applied
    // to two args in the body (each application beta-reduces both binders).
    ctx.ok(&.{ "check", "tests/cases/schema_binary_param.bpa" }, "OK: 7 declarations, 2 theorems proven\n");

    // definite description (the tame ι) as an axiom-schema over a relational param:
    // a proven total+single-valued graph is realized by a function (`exists g`).
    ctx.ok(&.{ "check", "tests/cases/choice_description.bpa" }, "OK: 8 declarations, 1 theorems proven\n");

    // the `case` construct: a 3-way disjunction split checks with every step kernel-checked
    ctx.ok(&.{ "check", "tests/cases/case_split.bpa" }, "OK: 11 declarations, 1 theorems proven\n");

    // a `case` arm assuming the wrong disjunct is a located error
    ctx.fail(&.{ "check", "tests/cases/case_bad_arm.bpa" }, "tests/cases/case_bad_arm.bpa:20:16: error: case arm assumes 'q(Z)', but the disjunct here is 'p(Z)'\n");

    // forall_elim at several arguments emits the chain in one written step
    ctx.ok(&.{ "check", "tests/cases/forall_elim_multi.bpa" }, "OK: 5 declarations, 1 theorems proven\n");

    // no-shadowing rule: disjoint sibling subproofs may reuse a fix var
    ctx.ok(&.{ "check", "tests/cases/fix_sibling_reuse.bpa" }, "OK: 9 declarations, 2 theorems proven\n");

    // no-shadowing rule for labels: an inner label shadowing an enclosing
    // one is an error (disjoint sibling reuse stays fine)
    ctx.fail(&.{ "check", "tests/cases/label_shadow_bad.bpa" }, "tests/cases/label_shadow_bad.bpa:17:8: error: label 'base' shadows an enclosing label; choose a fresh name\n");

    // the forward manifest is checked: promised theorems must exist
    ctx.fail(&.{ "check", "tests/cases/forward_bad.bpa" },
        \\tests/cases/forward_bad.bpa:3:9: error: forwarded theorem 'missingTheorem' is never defined
        \\tests/cases/forward_bad.bpa:4:9: error: 'onlyAxiom' is forwarded as a theorem but defined as an axiom
        \\
    );

    // `define` abbreviations expand transparently; certificates unaffected
    ctx.ok(&.{ "check", "tests/cases/define.bpa" }, "OK: 9 declarations, 1 theorems proven\n");

    // defines share the declaration namespace
    ctx.fail(&.{ "check", "tests/cases/define_bad.bpa" }, "tests/cases/define_bad.bpa:5:8: error: duplicate declaration of 'TWO'\n");

    // the outline fixture is itself a valid proof
    ctx.ok(&.{ "check", "tests/cases/outline.bpa" }, "OK: 8 declarations, 1 theorems proven\n");

    // the search fixture is itself a valid proof
    ctx.ok(&.{ "check", "tests/cases/search_target.bpa" }, "OK: 8 declarations, 1 theorems proven\n");

    // an error in an embedded proof maps to the .md's OWN line number
    // (prose-masking preserves line offsets).
    ctx.fail(&.{ "check", "tests/cases/literate_bad.md" }, "tests/cases/literate_bad.md:16:4: error: reflexivity requires a claim of the form 't = t', got 'A = B'\n");

    // M5: guards discharged by hypothesis and by matching lemma
    ctx.okSilent(&.{ "check", "tests/cases/div_ok.bpa" });

    // M5: unguarded division is rejected with the exact obligation
    ctx.fail(&.{ "check", "tests/cases/div_bad.bpa" },
        \\tests/cases/div_bad.bpa:7:14: error: unproved obligation: 'ZERO != ZERO'
        \\tests/cases/div_bad.bpa:7:31: error: unproved obligation: 'ZERO != ZERO'
        \\
    );

    // M5: nested guarded applications report every obligation
    ctx.fail(&.{ "check", "tests/cases/div_nested.bpa" },
        \\tests/cases/div_nested.bpa:6:16: error: unproved obligation: 'div(ZERO, ZERO) != ZERO'
        \\tests/cases/div_nested.bpa:6:26: error: unproved obligation: 'ZERO != ZERO'
        \\
    );

    // Review fix: not_intro may only cite steps available at the END of
    // the cited subproof, not inside deeper nested assumptions
    ctx.fail(&.{ "check", "tests/cases/not_intro_nested_bad.bpa" }, "tests/cases/not_intro_nested_bad.bpa:24:21: error: not_intro: 's1' is not accessible at the conclusion of the cited subproof\n");

    // Review fix: a block whose only content is a nested subproof has no
    // conclusion to discharge (was: kernel panic)
    ctx.fail(&.{ "check", "tests/cases/no_conclusion_bad.bpa" }, "tests/cases/no_conclusion_bad.bpa:18:23: error: subproof 'b' has no concluding step of its own\n");

    // `hole`: an aspirational axiom-shaped placeholder. Default mode REJECTS a
    // file that rests on one, enumerating each hole with its location and the
    // theorems that depend on it.
    ctx.fail(&.{ "check", "tests/cases/hole.bpa" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - zeroIsEven  (tests/cases/hole.bpa:10)  — rested on by: restsOnHole
        \\
    );
    // --draft allows holes (exit 0) with a loud disclosure banner naming them.
    ctx.ok(&.{ "check", "--draft", "tests/cases/hole.bpa" },
        \\OK: 6 declarations, 1 theorems proven
        \\  — DRAFT — 1 hole(s) unfilled (aspirational; the result is conditional on them): zeroIsEven; re-run `bpa check` (no --draft) once filled.
        \\
    );
    // holes are ORTHOGONAL to acceleration: --fast alone still rejects them.
    ctx.fail(&.{ "check", "--fast", "tests/cases/hole.bpa" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - zeroIsEven  (tests/cases/hole.bpa:10)  — rested on by: restsOnHole
        \\
    );
    // holes propagate transitively across imports: a theorem citing a
    // hole-tainted theorem inherits the hole (blast radius shows both).
    ctx.fail(&.{ "check", "tests/cases/hole_transitive.bpa" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - zeroIsEven  (tests/cases/hole.bpa:10)  — rested on by: restsOnHole, transitiveHole
        \\
    );
}
