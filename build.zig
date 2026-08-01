const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Core library module: all proof-checking logic lives here; main.zig is a thin CLI.
    const mod = b.addModule("bpa", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
    });

    const exe = b.addExecutable(.{
        .name = "bpa",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "bpa", .module = mod },
            },
        }),
    });
    b.installArtifact(exe);

    const run_step = b.step("run", "Run bpa");
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);

    // Unit tests (library + CLI modules).
    const mod_tests = b.addTest(.{ .root_module = mod });
    const run_mod_tests = b.addRunArtifact(mod_tests);
    const exe_tests = b.addTest(.{ .root_module = exe.root_module });
    const run_exe_tests = b.addRunArtifact(exe_tests);

    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_mod_tests.step);
    test_step.dependOn(&run_exe_tests.step);

    // CLI smoke tests: pin the command-line contract (exit codes + diagnostics stream).
    {
        // No arguments -> usage on stderr, exit 1.
        const no_args = b.addRunArtifact(exe);
        no_args.has_side_effects = true;
        no_args.expectStdErrEqual(
            "usage: bpa check [--fast | --faster | --reckless] <file.bpa>\n" ++
                "       bpa fmt [--check] <file.bpa>\n" ++
                "       bpa query outline <file.bpa> [theorem]\n" ++
                "       bpa query theorem <file.bpa> <theorem> [--sig]\n" ++
                "       bpa query whereis <file.bpa> <identifier>\n" ++
                "       bpa query search <file.bpa|dir> <query>\n" ++
                "       bpa query uses <file.bpa> [theorem]\n" ++
                "       bpa query oracles <file.bpa> [theorem]\n",
        );
        no_args.expectExitCode(1);
        test_step.dependOn(&no_args.step);

        // fmt --check: the exemplars are canonically formatted
        for ([_][]const u8{ "examples/peano.bpa", "examples/peano-pure.bpa", "examples/peano-imports.bpa", "examples/gauss.bpa", "examples/gauss-pure.bpa", "examples/euclid.bpa", "examples/euclid-compute.bpa", "examples/incorrect.bpa", "examples/sqrt2.bpa", "std/peano.bpa", "std/peano-ordering.bpa", "std/peano-subtraction.bpa", "std/peano-division.bpa", "std/peano-gcd.bpa", "std/peano-parity.bpa", "std/group.bpa", "std/set.bpa", "std/function.bpa", "tests/cases/kebab_label_ok.bpa", "tests/cases/schema_eta.bpa", "tests/cases/case_split.bpa", "tests/cases/fix_sibling_reuse.bpa", "tests/cases/outline.bpa", "tests/cases/assoc_commut_custom.bpa", "tests/cases/assoc_commut_bad_arity.bpa", "tests/cases/assoc_commut_oracle.bpa", "tests/cases/polynomial_oracle.bpa", "tests/cases/search_target.bpa", "tests/cases/assoc.bpa", "tests/cases/assoc_bad.bpa", "tests/cases/assoc_missing_arg.bpa", "tests/cases/assoc_oracle.bpa", "tests/cases/axiom_as_step_bad.bpa" }) |path| {
            const fmt_check = b.addRunArtifact(exe);
            fmt_check.has_side_effects = true;
            fmt_check.setCwd(b.path("."));
            fmt_check.addArgs(&.{ "fmt", "--check", path });
            fmt_check.expectStdErrEqual("");
            fmt_check.expectExitCode(0);
            test_step.dependOn(&fmt_check.step);
        }

        // Nonexistent file -> clean diagnostic on stderr, exit 1.
        const missing = b.addRunArtifact(exe);
        missing.has_side_effects = true;
        missing.addArgs(&.{ "check", "nosuchfile.bpa" });
        missing.expectStdErrEqual("error: cannot open 'nosuchfile.bpa': file not found\n");
        missing.expectExitCode(1);
        test_step.dependOn(&missing.step);

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
        const syn = b.addRunArtifact(exe);
        syn.has_side_effects = true;
        syn.setCwd(b.path("."));
        syn.addArgs(&.{ "check", "tests/cases/syntax_err.bpa" });
        syn.expectStdErrEqual(
            "tests/cases/syntax_err.bpa:4:11: error: expected ':', got 'forall'\n",
        );
        syn.expectExitCode(1);
        test_step.dependOn(&syn.step);

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
        const mismatch = b.addRunArtifact(exe);
        mismatch.has_side_effects = true;
        mismatch.setCwd(b.path("."));
        mismatch.addArgs(&.{ "check", "tests/cases/sort_mismatch.bpa" });
        mismatch.expectStdErrEqual(
            "tests/cases/sort_mismatch.bpa:5:17: error: expected sort 'Nat', got 'Prop'\n",
        );
        mismatch.expectExitCode(1);
        test_step.dependOn(&mismatch.step);

        // M3: proofs that must check
        for ([_][]const u8{
            "tests/cases/modus_ponens.bpa",
            "tests/cases/imp_chain.bpa",
            "tests/cases/forall_swap.bpa",
        }) |path| {
            const good = b.addRunArtifact(exe);
            good.has_side_effects = true;
            good.setCwd(b.path("."));
            good.addArgs(&.{ "check", path });
            good.expectStdErrEqual("");
            good.expectExitCode(0);
            test_step.dependOn(&good.step);
        }

        // M3: broken siblings with exact diagnostics
        const mp_bad = b.addRunArtifact(exe);
        mp_bad.has_side_effects = true;
        mp_bad.setCwd(b.path("."));
        mp_bad.addArgs(&.{ "check", "tests/cases/modus_ponens_bad.bpa" });
        mp_bad.expectStdErrEqual(
            "tests/cases/modus_ponens_bad.bpa:16:22: error: modus_ponens expects an implication, got 'p'\n",
        );
        mp_bad.expectExitCode(1);
        test_step.dependOn(&mp_bad.step);

        // citing an axiom where a proof STEP is required: the diagnostic must
        // point at the fix (materialize it as a step first), not report a bare
        // "unknown reference".
        const axiom_as_step = b.addRunArtifact(exe);
        axiom_as_step.has_side_effects = true;
        axiom_as_step.setCwd(b.path("."));
        axiom_as_step.addArgs(&.{ "check", "tests/cases/axiom_as_step_bad.bpa" });
        axiom_as_step.expectStdErrEqual(
            "tests/cases/axiom_as_step_bad.bpa:14:24: error: 'pall' is an axiom, not a proof step; introduce it as a step first with `[by axiom pall]`, then reference that step\n",
        );
        axiom_as_step.expectExitCode(1);
        test_step.dependOn(&axiom_as_step.step);

        const shadow_bad = b.addRunArtifact(exe);
        shadow_bad.has_side_effects = true;
        shadow_bad.setCwd(b.path("."));
        shadow_bad.addArgs(&.{ "check", "tests/cases/fix_shadow_bad.bpa" });
        shadow_bad.expectStdErrEqual(
            "tests/cases/fix_shadow_bad.bpa:10:13: error: 'a' shadows an enclosing variable; choose a fresh name\n",
        );
        shadow_bad.expectExitCode(1);
        test_step.dependOn(&shadow_bad.step);

        // the living demo: automation-assisted PA — simplify inside the
        // inductions, pure arithmetic certificates, and one oracle step that
        // needs --fast (until the Farkas certificate lands); the loud banner
        // discloses the deferred verification.
        const pa = b.addRunArtifact(exe);
        pa.has_side_effects = true;
        pa.setCwd(b.path("."));
        pa.addArgs(&.{ "check", "--fast", "examples/peano.bpa" });
        pa.expectStdErrEqual("");
        pa.expectStdOutEqual("OK: 18 declarations, 6 theorems proven (5 pure, 1 via oracles: arithmetic)\n" ++
            "  \u{2014} NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.\n");
        pa.expectExitCode(0);
        test_step.dependOn(&pa.step);

        // ...and under the DEFAULT (verify everything), that oracle step is a
        // hard error pointing at --fast.
        const pa_default = b.addRunArtifact(exe);
        pa_default.has_side_effects = true;
        pa_default.setCwd(b.path("."));
        pa_default.addArgs(&.{ "check", "examples/peano.bpa" });
        // the evenOrOdd oracle step (∀∃, Cooper-QE) is decided valid but no
        // certifier can prove it; the terminal lists each link's decline reason
        // (Farkas needs less_than, absent in peano.bpa's local scope).
        pa_default.expectStdErrEqual(
            "examples/peano.bpa:182:9: error: 'arithmetic' is valid but no certifier could prove it here:\n" ++
                "  - equation/order/exists: form not in certification scope\n" ++
                "  - mixed-skeleton: form not in certification scope\n" ++
                "  - farkas: theory lacks symbol 'less_than'\n" ++
                "use --fast to accept the oracle verdict\n",
        );
        pa_default.expectExitCode(1);
        test_step.dependOn(&pa_default.step);

        // the by-hand twin: every induction case in primitive rules
        const pa_pure = b.addRunArtifact(exe);
        pa_pure.has_side_effects = true;
        pa_pure.setCwd(b.path("."));
        pa_pure.addArgs(&.{ "check", "examples/peano-pure.bpa" });
        pa_pure.expectStdErrEqual("");
        pa_pure.expectStdOutEqual("OK: 13 declarations, 3 theorems proven\n");
        pa_pure.expectExitCode(0);
        test_step.dependOn(&pa_pure.step);

        // M6: --help
        const help = b.addRunArtifact(exe);
        help.has_side_effects = true;
        help.addArg("--help");
        help.expectExitCode(0);
        test_step.dependOn(&help.step);

        // the incorrect-proof showcase: three classic mistakes, three exact
        // diagnostics (this file is documentation; its output is the contract)
        const incorrect = b.addRunArtifact(exe);
        incorrect.has_side_effects = true;
        incorrect.setCwd(b.path("."));
        incorrect.addArgs(&.{ "check", "examples/incorrect.bpa" });
        incorrect.expectStdErrEqual(
            "examples/incorrect.bpa:39:41: error: modus_ponens: expected antecedent 'raining', got 'wet'\n" ++
                "examples/incorrect.bpa:61:4: error: step claims 'forall n: Nat; is_zero(n)' but forall_intro derives 'forall n: Nat; is_zero(ZERO)'\n" ++
                "examples/incorrect.bpa:73:28: error: unproved obligation: 'ZERO != ZERO'\n",
        );
        incorrect.expectExitCode(1);
        test_step.dependOn(&incorrect.step);

        // M4: ill-sorted schema argument dies at the use site
        const bad_sort = b.addRunArtifact(exe);
        bad_sort.has_side_effects = true;
        bad_sort.setCwd(b.path("."));
        bad_sort.addArgs(&.{ "check", "tests/cases/induction_bad_sort.bpa" });
        bad_sort.expectStdErrEqual(
            "tests/cases/induction_bad_sort.bpa:14:46: error: expected a proposition, got sort 'Nat'\n",
        );
        bad_sort.expectExitCode(1);
        test_step.dependOn(&bad_sort.step);

        // M4: proof-carrying schema fails only at the failing instantiation
        const per_inst = b.addRunArtifact(exe);
        per_inst.has_side_effects = true;
        per_inst.setCwd(b.path("."));
        per_inst.addArgs(&.{ "check", "tests/cases/schema_per_instance.bpa" });
        per_inst.expectStdErrEqual(
            "tests/cases/schema_per_instance.bpa:10:4: error: reflexivity requires a claim of the form 't = t', got 'succ(ZERO) = ZERO'\n" ++
                "tests/cases/schema_per_instance.bpa:29:21: error: instantiation of schema 'zeroLike' failed here\n",
        );
        per_inst.expectExitCode(1);
        test_step.dependOn(&per_inst.step);

        // forward label references: a step may cite a later-defined label
        const forward_ref = b.addRunArtifact(exe);
        forward_ref.has_side_effects = true;
        forward_ref.setCwd(b.path("."));
        forward_ref.addArgs(&.{ "check", "tests/cases/forward_ref.bpa" });
        forward_ref.expectStdErrEqual("");
        forward_ref.expectStdOutEqual("OK: 6 declarations, 1 theorems proven\n");
        forward_ref.expectExitCode(0);
        test_step.dependOn(&forward_ref.step);

        // mutually-citing steps form a justification cycle, reported by name
        const forward_cycle = b.addRunArtifact(exe);
        forward_cycle.has_side_effects = true;
        forward_cycle.setCwd(b.path("."));
        forward_cycle.addArgs(&.{ "check", "tests/cases/forward_ref_cycle.bpa" });
        forward_cycle.expectStdErrEqual(
            "tests/cases/forward_ref_cycle.bpa:10:4: error: cyclic justification: a -> b -> a\n",
        );
        forward_cycle.expectExitCode(1);
        test_step.dependOn(&forward_cycle.step);

        // a self-instantiating schema is a named cycle, not a blunt depth cap
        const schema_cycle = b.addRunArtifact(exe);
        schema_cycle.has_side_effects = true;
        schema_cycle.setCwd(b.path("."));
        schema_cycle.addArgs(&.{ "check", "tests/cases/schema_cycle.bpa" });
        schema_cycle.expectStdErrEqual(
            "tests/cases/schema_cycle.bpa:11:21: error: schema instantiation cycle: loopy -> loopy\n" ++
                "tests/cases/schema_cycle.bpa:19:21: error: instantiation of schema 'loopy' failed here\n",
        );
        schema_cycle.expectExitCode(1);
        test_step.dependOn(&schema_cycle.step);

        // a deep but terminating instantiation chain (10 distinct schemas) is
        // accepted — the old inst_depth cap wrongly rejected it
        const schema_deep = b.addRunArtifact(exe);
        schema_deep.has_side_effects = true;
        schema_deep.setCwd(b.path("."));
        schema_deep.addArgs(&.{ "check", "tests/cases/schema_deep_ok.bpa" });
        schema_deep.expectStdErrEqual("");
        schema_deep.expectStdOutEqual("OK: 12 declarations, 1 theorems proven\n");
        schema_deep.expectExitCode(0);
        test_step.dependOn(&schema_deep.step);

        // kebab-case is rejected in a declaration-name position (parser)
        const kebab_decl = b.addRunArtifact(exe);
        kebab_decl.has_side_effects = true;
        kebab_decl.setCwd(b.path("."));
        kebab_decl.addArgs(&.{ "check", "tests/cases/kebab_decl_bad.bpa" });
        kebab_decl.expectStdErrEqual("tests/cases/kebab_decl_bad.bpa:6:6: error: expected 'identifier', got 'foo-bar'\n");
        kebab_decl.expectExitCode(1);
        test_step.dependOn(&kebab_decl.step);

        // kebab-case IS allowed for proof labels and [by ...] references
        const kebab_label = b.addRunArtifact(exe);
        kebab_label.has_side_effects = true;
        kebab_label.setCwd(b.path("."));
        kebab_label.addArgs(&.{ "check", "tests/cases/kebab_label_ok.bpa" });
        kebab_label.expectStdErrEqual("");
        kebab_label.expectStdOutEqual("OK: 4 declarations, 1 theorems proven\n");
        kebab_label.expectExitCode(0);
        test_step.dependOn(&kebab_label.step);

        // eta-sugar: a schema Nat->Prop param accepts a bare predicate name
        const schema_eta = b.addRunArtifact(exe);
        schema_eta.has_side_effects = true;
        schema_eta.setCwd(b.path("."));
        schema_eta.addArgs(&.{ "check", "tests/cases/schema_eta.bpa" });
        schema_eta.expectStdErrEqual("");
        schema_eta.expectStdOutEqual("OK: 8 declarations, 1 theorems proven\n");
        schema_eta.expectExitCode(0);
        test_step.dependOn(&schema_eta.step);

        // the `case` construct: a 3-way disjunction split checks pure
        const case_split = b.addRunArtifact(exe);
        case_split.has_side_effects = true;
        case_split.setCwd(b.path("."));
        case_split.addArgs(&.{ "check", "tests/cases/case_split.bpa" });
        case_split.expectStdErrEqual("");
        case_split.expectStdOutEqual("OK: 11 declarations, 1 theorems proven\n");
        case_split.expectExitCode(0);
        test_step.dependOn(&case_split.step);

        // a `case` arm assuming the wrong disjunct is a located error
        const case_bad = b.addRunArtifact(exe);
        case_bad.has_side_effects = true;
        case_bad.setCwd(b.path("."));
        case_bad.addArgs(&.{ "check", "tests/cases/case_bad_arm.bpa" });
        case_bad.expectStdErrEqual("tests/cases/case_bad_arm.bpa:20:16: error: case arm assumes 'q(Z)', but the disjunct here is 'p(Z)'\n");
        case_bad.expectExitCode(1);
        test_step.dependOn(&case_bad.step);

        // forall_elim at several arguments emits the chain in one written step
        const multi_elim = b.addRunArtifact(exe);
        multi_elim.has_side_effects = true;
        multi_elim.setCwd(b.path("."));
        multi_elim.addArgs(&.{ "check", "tests/cases/forall_elim_multi.bpa" });
        multi_elim.expectStdErrEqual("");
        multi_elim.expectStdOutEqual("OK: 5 declarations, 1 theorems proven\n");
        multi_elim.expectExitCode(0);
        test_step.dependOn(&multi_elim.step);

        // no-shadowing rule: disjoint sibling subproofs may reuse a fix var
        const fix_reuse = b.addRunArtifact(exe);
        fix_reuse.has_side_effects = true;
        fix_reuse.setCwd(b.path("."));
        fix_reuse.addArgs(&.{ "check", "tests/cases/fix_sibling_reuse.bpa" });
        fix_reuse.expectStdErrEqual("");
        fix_reuse.expectStdOutEqual("OK: 9 declarations, 2 theorems proven\n");
        fix_reuse.expectExitCode(0);
        test_step.dependOn(&fix_reuse.step);

        // no-shadowing rule for labels: an inner label shadowing an enclosing
        // one is an error (disjoint sibling reuse stays fine)
        const label_shadow = b.addRunArtifact(exe);
        label_shadow.has_side_effects = true;
        label_shadow.setCwd(b.path("."));
        label_shadow.addArgs(&.{ "check", "tests/cases/label_shadow_bad.bpa" });
        label_shadow.expectStdErrEqual("tests/cases/label_shadow_bad.bpa:17:8: error: label 'base' shadows an enclosing label; choose a fresh name\n");
        label_shadow.expectExitCode(1);
        test_step.dependOn(&label_shadow.step);

        // the forward manifest is checked: promised theorems must exist
        const fwd_bad = b.addRunArtifact(exe);
        fwd_bad.has_side_effects = true;
        fwd_bad.setCwd(b.path("."));
        fwd_bad.addArgs(&.{ "check", "tests/cases/forward_bad.bpa" });
        fwd_bad.expectStdErrEqual(
            "tests/cases/forward_bad.bpa:3:9: error: forwarded theorem 'missingTheorem' is never defined\n" ++
                "tests/cases/forward_bad.bpa:4:9: error: 'onlyAxiom' is forwarded as a theorem but defined as an axiom\n",
        );
        fwd_bad.expectExitCode(1);
        test_step.dependOn(&fwd_bad.step);

        // Milestone A: simplify — certificate-producing rewrite tactic
        const simp = b.addRunArtifact(exe);
        simp.has_side_effects = true;
        simp.setCwd(b.path("."));
        simp.addArgs(&.{ "check", "tests/cases/simplify.bpa" });
        simp.expectStdErrEqual("");
        simp.expectStdOutEqual("OK: 13 declarations, 2 theorems proven\n");
        simp.expectExitCode(0);
        test_step.dependOn(&simp.step);

        // simplify is pure (never an oracle): --pure must accept it
        const simp_pure = b.addRunArtifact(exe);
        simp_pure.has_side_effects = true;
        simp_pure.setCwd(b.path("."));
        simp_pure.addArgs(&.{ "check", "tests/cases/simplify.bpa" });
        simp_pure.expectStdErrEqual("");
        simp_pure.expectStdOutEqual("OK: 13 declarations, 2 theorems proven\n");
        simp_pure.expectExitCode(0);
        test_step.dependOn(&simp_pure.step);

        // unjoinable normal forms: the diagnostic shows both, copy-pasteable
        const simp_bad = b.addRunArtifact(exe);
        simp_bad.has_side_effects = true;
        simp_bad.setCwd(b.path("."));
        simp_bad.addArgs(&.{ "check", "tests/cases/simplify_bad.bpa" });
        simp_bad.expectStdErrEqual(
            "tests/cases/simplify_bad.bpa:14:13: error: simplify: normal forms differ: 'add(n, ZERO)' vs 'n'\n",
        );
        simp_bad.expectExitCode(1);
        test_step.dependOn(&simp_bad.step);

        // cycling rules hit the hard rewrite cap instead of hanging
        const simp_loop = b.addRunArtifact(exe);
        simp_loop.has_side_effects = true;
        simp_loop.setCwd(b.path("."));
        simp_loop.addArgs(&.{ "check", "tests/cases/simplify_loop.bpa" });
        simp_loop.expectStdErrEqual(
            "tests/cases/simplify_loop.bpa:13:9: error: simplify: rewrite limit reached (looping rule set?)\n",
        );
        simp_loop.expectExitCode(1);
        test_step.dependOn(&simp_loop.step);

        // ac: associative-commutative sum reordering over opaque atoms, pure
        const ac = b.addRunArtifact(exe);
        ac.has_side_effects = true;
        ac.setCwd(b.path("."));
        ac.addArgs(&.{ "check", "tests/cases/ac.bpa" });
        ac.expectStdErrEqual("");
        ac.expectStdOutEqual("OK: 59 declarations, 19 theorems proven\n");
        ac.expectExitCode(0);
        test_step.dependOn(&ac.step);

        // ac over multiplication: same bubble-sort machinery, mul lemma triple
        // (mulIsAssociative/mulIsCommutative/mulLeftSwap), pure
        const ac_mul = b.addRunArtifact(exe);
        ac_mul.has_side_effects = true;
        ac_mul.setCwd(b.path("."));
        ac_mul.addArgs(&.{ "check", "tests/cases/ac_mul.bpa" });
        ac_mul.expectStdErrEqual("");
        ac_mul.expectStdOutEqual("OK: 59 declarations, 18 theorems proven\n");
        ac_mul.expectExitCode(0);
        test_step.dependOn(&ac_mul.step);

        // ac_quantified: peel the forall prefix then run the ac core (add + mul)
        const ac_q = b.addRunArtifact(exe);
        ac_q.has_side_effects = true;
        ac_q.setCwd(b.path("."));
        ac_q.addArgs(&.{ "check", "tests/cases/ac_quantified.bpa" });
        ac_q.expectStdErrEqual("");
        ac_q.expectStdOutEqual("OK: 60 declarations, 19 theorems proven\n");
        ac_q.expectExitCode(0);
        test_step.dependOn(&ac_q.step);

        // distributivity: ac_quantified with a cited distributivity lemma
        // pre-normalizes (distributes) each side before the AC bubble-sort
        const distribute = b.addRunArtifact(exe);
        distribute.has_side_effects = true;
        distribute.setCwd(b.path("."));
        distribute.addArgs(&.{ "check", "tests/cases/distribute.bpa" });
        distribute.expectStdErrEqual("");
        distribute.expectStdOutEqual("OK: 57 declarations, 18 theorems proven\n");
        distribute.expectExitCode(0);
        test_step.dependOn(&distribute.step);

        // `polynomial(theory)`: nonlinear identities canonicalize pure (no
        // oracle) via distribute → sort monomials → sort sum → fold.
        const polynomial = b.addRunArtifact(exe);
        polynomial.has_side_effects = true;
        polynomial.setCwd(b.path("."));
        polynomial.addArgs(&.{ "check", "tests/cases/polynomial.bpa" });
        polynomial.expectStdErrEqual("");
        polynomial.expectStdOutEqual("OK: 54 declarations, 19 theorems proven\n");
        polynomial.expectExitCode(0);
        test_step.dependOn(&polynomial.step);

        // sides with different expansions → located error, exit 1 (no taint)
        const polynomial_bad = b.addRunArtifact(exe);
        polynomial_bad.has_side_effects = true;
        polynomial_bad.setCwd(b.path("."));
        polynomial_bad.addArgs(&.{ "check", "tests/cases/polynomial_bad.bpa" });
        polynomial_bad.expectStdErrEqual("tests/cases/polynomial_bad.bpa:18:9: error: polynomial: sides expand differently: 'add(mul(poly, poly), add(mul(poly, poly), add(mul(poly, poly), mul(poly, poly))))' vs 'add(mul(poly, poly), mul(poly, poly))'\n");
        polynomial_bad.expectExitCode(1);
        test_step.dependOn(&polynomial_bad.step);

        // the polynomial ORACLE: a thin theory (no ring lemmas) DECLINES under
        // the default (needs a lemma), but --fast decides it structurally and
        // taints (via oracles: polynomial).
        const poly_oracle_default = b.addRunArtifact(exe);
        poly_oracle_default.has_side_effects = true;
        poly_oracle_default.setCwd(b.path("."));
        poly_oracle_default.addArgs(&.{ "check", "tests/cases/polynomial_oracle.bpa" });
        poly_oracle_default.expectStdErrEqual("tests/cases/polynomial_oracle.bpa:22:9: error: polynomial: needs mulAddDistribLeft in scope\n");
        poly_oracle_default.expectExitCode(1);
        test_step.dependOn(&poly_oracle_default.step);

        const poly_oracle_fast = b.addRunArtifact(exe);
        poly_oracle_fast.has_side_effects = true;
        poly_oracle_fast.setCwd(b.path("."));
        poly_oracle_fast.addArgs(&.{ "check", "--fast", "tests/cases/polynomial_oracle.bpa" });
        poly_oracle_fast.expectStdErrEqual("");
        poly_oracle_fast.expectStdOutEqual("OK: 6 declarations, 1 theorems proven (0 pure, 1 via oracles: polynomial)\n  — NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.\n");
        poly_oracle_fast.expectExitCode(0);
        test_step.dependOn(&poly_oracle_fast.step);

        // ac on different multisets reports the mismatch (pure, no taint)
        const ac_bad = b.addRunArtifact(exe);
        ac_bad.has_side_effects = true;
        ac_bad.setCwd(b.path("."));
        ac_bad.addArgs(&.{ "check", "tests/cases/ac_bad.bpa" });
        ac_bad.expectStdErrEqual(
            "tests/cases/ac_bad.bpa:18:17: error: assoc_commut: sides have different summands: 'add(b, add(a, a))' vs 'add(b, a)'\n",
        );
        ac_bad.expectExitCode(1);
        test_step.dependOn(&ac_bad.step);

        // assoc_commut(assoc, comm, swap): the explicit-triple form on a CUSTOM
        // operator (pure — the triple is kernel-checked).
        const ac_custom = b.addRunArtifact(exe);
        ac_custom.has_side_effects = true;
        ac_custom.setCwd(b.path("."));
        ac_custom.addArgs(&.{ "check", "tests/cases/assoc_commut_custom.bpa" });
        ac_custom.expectStdErrEqual("");
        ac_custom.expectStdOutEqual("OK: 7 declarations, 2 theorems proven\n");
        ac_custom.expectExitCode(0);
        test_step.dependOn(&ac_custom.step);

        // no partials: 1 or 2 args is an error (either bare or exactly three).
        const ac_arity = b.addRunArtifact(exe);
        ac_arity.has_side_effects = true;
        ac_arity.setCwd(b.path("."));
        ac_arity.addArgs(&.{ "check", "tests/cases/assoc_commut_bad_arity.bpa" });
        ac_arity.expectStdErrEqual("tests/cases/assoc_commut_bad_arity.bpa:12:9: error: assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got 2\n");
        ac_arity.expectExitCode(1);
        test_step.dependOn(&ac_arity.step);

        // the assoc_commut ORACLE: bare form on a thin theory (no AC lemmas)
        // DECLINES by default, but --fast decides structurally and taints.
        const ac_oracle_default = b.addRunArtifact(exe);
        ac_oracle_default.has_side_effects = true;
        ac_oracle_default.setCwd(b.path("."));
        ac_oracle_default.addArgs(&.{ "check", "tests/cases/assoc_commut_oracle.bpa" });
        ac_oracle_default.expectStdErrEqual("tests/cases/assoc_commut_oracle.bpa:16:9: error: assoc_commut: needs addIsAssociative in scope\n");
        ac_oracle_default.expectExitCode(1);
        test_step.dependOn(&ac_oracle_default.step);

        const ac_oracle_fast = b.addRunArtifact(exe);
        ac_oracle_fast.has_side_effects = true;
        ac_oracle_fast.setCwd(b.path("."));
        ac_oracle_fast.addArgs(&.{ "check", "--fast", "tests/cases/assoc_commut_oracle.bpa" });
        ac_oracle_fast.expectStdErrEqual("");
        ac_oracle_fast.expectStdOutEqual("OK: 4 declarations, 1 theorems proven (0 pure, 1 via oracles: assoc_commut)\n  — NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.\n");
        ac_oracle_fast.expectExitCode(0);
        test_step.dependOn(&ac_oracle_fast.step);

        // `assoc(assocLemma)`: associativity-only reorder on a CUSTOM operator
        // (no add/mul assumption). Pure.
        const assoc_t = b.addRunArtifact(exe);
        assoc_t.has_side_effects = true;
        assoc_t.setCwd(b.path("."));
        assoc_t.addArgs(&.{ "check", "tests/cases/assoc.bpa" });
        assoc_t.expectStdErrEqual("");
        assoc_t.expectStdOutEqual("OK: 6 declarations, 3 theorems proven\n");
        assoc_t.expectExitCode(0);
        test_step.dependOn(&assoc_t.step);

        // sides differ by more than associativity (operands permuted) → error
        const assoc_bad = b.addRunArtifact(exe);
        assoc_bad.has_side_effects = true;
        assoc_bad.setCwd(b.path("."));
        assoc_bad.addArgs(&.{ "check", "tests/cases/assoc_bad.bpa" });
        assoc_bad.expectStdErrEqual("tests/cases/assoc_bad.bpa:11:9: error: assoc: sides differ by more than associativity: 'op(assoc, assoc)' vs 'op(assoc, assoc)'\n");
        assoc_bad.expectExitCode(1);
        test_step.dependOn(&assoc_bad.step);

        // the required-arg contract: bare `assoc` is an error
        const assoc_missing = b.addRunArtifact(exe);
        assoc_missing.has_side_effects = true;
        assoc_missing.setCwd(b.path("."));
        assoc_missing.addArgs(&.{ "check", "tests/cases/assoc_missing_arg.bpa" });
        assoc_missing.expectStdErrEqual("tests/cases/assoc_missing_arg.bpa:10:9: error: assoc requires an associativity lemma: assoc(<assocLemma>); got 0 argument(s)\n");
        assoc_missing.expectExitCode(1);
        test_step.dependOn(&assoc_missing.step);

        // the assoc ORACLE: certifies by default, --fast taints
        const assoc_oracle_default = b.addRunArtifact(exe);
        assoc_oracle_default.has_side_effects = true;
        assoc_oracle_default.setCwd(b.path("."));
        assoc_oracle_default.addArgs(&.{ "check", "tests/cases/assoc_oracle.bpa" });
        assoc_oracle_default.expectStdErrEqual("");
        assoc_oracle_default.expectStdOutEqual("OK: 4 declarations, 1 theorems proven\n");
        assoc_oracle_default.expectExitCode(0);
        test_step.dependOn(&assoc_oracle_default.step);

        const assoc_oracle_fast = b.addRunArtifact(exe);
        assoc_oracle_fast.has_side_effects = true;
        assoc_oracle_fast.setCwd(b.path("."));
        assoc_oracle_fast.addArgs(&.{ "check", "--fast", "tests/cases/assoc_oracle.bpa" });
        assoc_oracle_fast.expectStdErrEqual("");
        assoc_oracle_fast.expectStdOutEqual("OK: 4 declarations, 1 theorems proven (0 pure, 1 via oracles: assoc)\n  — NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.\n");
        assoc_oracle_fast.expectExitCode(0);
        test_step.dependOn(&assoc_oracle_fast.step);

        // simplify_quantified: peel forall over an equation, pure
        const sq = b.addRunArtifact(exe);
        sq.has_side_effects = true;
        sq.setCwd(b.path("."));
        sq.addArgs(&.{ "check", "tests/cases/simplify_quantified.bpa" });
        sq.expectStdErrEqual("");
        sq.expectStdOutEqual("OK: 8 declarations, 2 theorems proven\n");
        sq.expectExitCode(0);
        test_step.dependOn(&sq.step);

        // simplify_quantified on a bare equation redirects to simplify
        const sq_bare = b.addRunArtifact(exe);
        sq_bare.has_side_effects = true;
        sq_bare.setCwd(b.path("."));
        sq_bare.addArgs(&.{ "check", "tests/cases/simplify_quantified_bad.bpa" });
        sq_bare.expectStdErrEqual(
            "tests/cases/simplify_quantified_bad.bpa:12:9: error: simplify_quantified expects a quantified goal; did you mean simplify?\n",
        );
        sq_bare.expectExitCode(1);
        test_step.dependOn(&sq_bare.step);

        // plain simplify on a quantified goal redirects to simplify_quantified
        const sq_quant = b.addRunArtifact(exe);
        sq_quant.has_side_effects = true;
        sq_quant.setCwd(b.path("."));
        sq_quant.addArgs(&.{ "check", "tests/cases/simplify_on_quantified.bpa" });
        sq_quant.expectStdErrEqual(
            "tests/cases/simplify_on_quantified.bpa:12:9: error: simplify proves equations; did you mean simplify_quantified?\n",
        );
        sq_quant.expectExitCode(1);
        test_step.dependOn(&sq_quant.step);

        // symmetry: y = x from x = y in one step, pure
        const symmetry = b.addRunArtifact(exe);
        symmetry.has_side_effects = true;
        symmetry.setCwd(b.path("."));
        symmetry.addArgs(&.{ "check", "tests/cases/symmetry.bpa" });
        symmetry.expectStdErrEqual("");
        symmetry.expectStdOutEqual("OK: 6 declarations, 1 theorems proven\n");
        symmetry.expectExitCode(0);
        test_step.dependOn(&symmetry.step);

        // Milestone B2: tautology emits certificates — kernel-checked steps,
        // no oracle, no taint (the oracle remains as the over-budget fallback)
        const taut = b.addRunArtifact(exe);
        taut.has_side_effects = true;
        taut.setCwd(b.path("."));
        taut.addArgs(&.{ "check", "tests/cases/tautology.bpa" });
        taut.expectStdErrEqual("");
        taut.expectStdOutEqual("OK: 9 declarations, 5 theorems proven\n");
        taut.expectExitCode(0);
        test_step.dependOn(&taut.step);

        // certificates satisfy --pure
        const taut_pure = b.addRunArtifact(exe);
        taut_pure.has_side_effects = true;
        taut_pure.setCwd(b.path("."));
        taut_pure.addArgs(&.{ "check", "tests/cases/tautology.bpa" });
        taut_pure.expectStdErrEqual("");
        taut_pure.expectStdOutEqual("OK: 9 declarations, 5 theorems proven\n");
        taut_pure.expectExitCode(0);
        test_step.dependOn(&taut_pure.step);

        // non-consequence: the diagnostic carries the countermodel
        const taut_bad = b.addRunArtifact(exe);
        taut_bad.has_side_effects = true;
        taut_bad.setCwd(b.path("."));
        taut_bad.addArgs(&.{ "check", "tests/cases/tautology_bad.bpa" });
        taut_bad.expectStdErrEqual(
            "tests/cases/tautology_bad.bpa:10:9: error: tautology: not a propositional consequence; countermodel: p := true, q := false\n",
        );
        taut_bad.expectExitCode(1);
        test_step.dependOn(&taut_bad.step);

        // the atom cap is a hard, honest limit
        const taut_cap = b.addRunArtifact(exe);
        taut_cap.has_side_effects = true;
        taut_cap.setCwd(b.path("."));
        taut_cap.addArgs(&.{ "check", "tests/cases/tautology_cap.bpa" });
        taut_cap.expectStdErrEqual(
            "tests/cases/tautology_cap.bpa:25:9: error: tautology: 17 distinct atoms exceeds the limit of 16\n",
        );
        taut_cap.expectExitCode(1);
        test_step.dependOn(&taut_cap.step);

        // Milestone C: arithmetic oracle — Presburger quantifier elimination
        const arith = b.addRunArtifact(exe);
        arith.has_side_effects = true;
        arith.setCwd(b.path("."));
        arith.addArgs(&.{ "check", "--fast", "tests/cases/arithmetic.bpa" });
        arith.expectStdErrEqual("");
        arith.expectStdOutEqual("OK: 9 declarations, 4 theorems proven (0 pure, 4 via oracles: arithmetic)\n" ++
            "  \u{2014} NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.\n");
        arith.expectExitCode(0);
        test_step.dependOn(&arith.step);

        // false statement: the diagnostic carries countermodel values
        const arith_bad = b.addRunArtifact(exe);
        arith_bad.has_side_effects = true;
        arith_bad.setCwd(b.path("."));
        arith_bad.addArgs(&.{ "check", "tests/cases/arithmetic_bad.bpa" });
        arith_bad.expectStdErrEqual(
            "tests/cases/arithmetic_bad.bpa:17:17: error: arithmetic: false at a := 0, b := 0\n",
        );
        arith_bad.expectExitCode(1);
        test_step.dependOn(&arith_bad.step);

        // a relation opaque only because it hides a nonlinear term is
        // reported honestly as outside the fragment, not as a false countermodel
        const arith_frag = b.addRunArtifact(exe);
        arith_frag.has_side_effects = true;
        arith_frag.setCwd(b.path("."));
        arith_frag.addArgs(&.{ "check", "tests/cases/arithmetic_frag.bpa" });
        arith_frag.expectStdErrEqual(
            "tests/cases/arithmetic_frag.bpa:15:9: error: arithmetic: 'mul(a, b)' is outside linear arithmetic\n",
        );
        arith_frag.expectExitCode(1);
        test_step.dependOn(&arith_frag.step);

        // Milestone D: the SMT combination — mixed goals, one oracle name
        const smt_mixed = b.addRunArtifact(exe);
        smt_mixed.has_side_effects = true;
        smt_mixed.setCwd(b.path("."));
        smt_mixed.addArgs(&.{ "check", "--fast", "tests/cases/smt.bpa" });
        smt_mixed.expectStdErrEqual("");
        smt_mixed.expectStdOutEqual("OK: 9 declarations, 2 theorems proven (0 pure, 2 via oracles: arithmetic)\n" ++
            "  \u{2014} NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.\n");
        smt_mixed.expectExitCode(0);
        test_step.dependOn(&smt_mixed.step);

        // Milestone C2b: universal linear goals replay as pure certificates
        // (sorted-sum normalization + synthesized order witnesses)
        const arith_cert2 = b.addRunArtifact(exe);
        arith_cert2.has_side_effects = true;
        arith_cert2.setCwd(b.path("."));
        arith_cert2.addArgs(&.{ "check", "tests/cases/arithmetic_cert2.bpa" });
        arith_cert2.expectStdErrEqual("");
        arith_cert2.expectStdOutEqual("OK: 146 declarations, 44 theorems proven\n");
        arith_cert2.expectExitCode(0);
        test_step.dependOn(&arith_cert2.step);

        // Farkas: difference-logic infeasibility (combine several order
        // hypotheses into a transitivity cycle) certifies purely under the
        // DEFAULT, via `arithmetic(<theory>)` resolving the order lemmas
        // against the named module — no local aliasing of the vocabulary.
        const farkas = b.addRunArtifact(exe);
        farkas.has_side_effects = true;
        farkas.setCwd(b.path("."));
        farkas.addArgs(&.{ "check", "tests/cases/farkas.bpa" });
        farkas.expectStdErrEqual("");
        farkas.expectStdOutEqual("OK: 122 declarations, 40 theorems proven\n");
        farkas.expectExitCode(0);
        test_step.dependOn(&farkas.step);

        // Farkas extensions: order composition (a<b -> b<c -> a<c, no cycle)
        // and the infeasibility cap (contradictory order hyps prove an
        // arbitrary conclusion via lessThanIrreflexive + absurd).
        const farkas_ext = b.addRunArtifact(exe);
        farkas_ext.has_side_effects = true;
        farkas_ext.setCwd(b.path("."));
        farkas_ext.addArgs(&.{ "check", "tests/cases/farkas_ext.bpa" });
        farkas_ext.expectStdErrEqual("");
        farkas_ext.expectStdOutEqual("OK: 124 declarations, 41 theorems proven\n");
        farkas_ext.expectExitCode(0);
        test_step.dependOn(&farkas_ext.step);

        // Farkas coefficient scaling (stage 1): a hypothesis scaled by a literal
        // via multiplicationPreservesOrder before the infeasibility fold.
        const farkas_scale = b.addRunArtifact(exe);
        farkas_scale.has_side_effects = true;
        farkas_scale.setCwd(b.path("."));
        farkas_scale.addArgs(&.{ "check", "tests/cases/farkas_scale.bpa" });
        farkas_scale.expectStdErrEqual("");
        farkas_scale.expectStdOutEqual("OK: 125 declarations, 39 theorems proven\n");
        farkas_scale.expectExitCode(0);
        test_step.dependOn(&farkas_scale.step);

        // Farkas sum path (stage 2): sum two order hypotheses over distinct
        // variables via additionPreservesOrder + commutativity + transitivity.
        const farkas_sum = b.addRunArtifact(exe);
        farkas_sum.has_side_effects = true;
        farkas_sum.setCwd(b.path("."));
        farkas_sum.addArgs(&.{ "check", "tests/cases/farkas_sum.bpa" });
        farkas_sum.expectStdErrEqual("");
        farkas_sum.expectStdOutEqual("OK: 122 declarations, 39 theorems proven\n");
        farkas_sum.expectExitCode(0);
        test_step.dependOn(&farkas_sum.step);

        // Milestone C2a: ground goals replay as pure simplify certificates
        // over the well-known peano axioms — --pure accepts them
        const arith_cert = b.addRunArtifact(exe);
        arith_cert.has_side_effects = true;
        arith_cert.setCwd(b.path("."));
        arith_cert.addArgs(&.{ "check", "tests/cases/arithmetic_cert.bpa" });
        arith_cert.expectStdErrEqual("");
        arith_cert.expectStdOutEqual("OK: 13 declarations, 2 theorems proven\n");
        arith_cert.expectExitCode(0);
        test_step.dependOn(&arith_cert.step);

        // Milestone D2: mixed skeletons replay as pure certificates
        const smt_cert = b.addRunArtifact(exe);
        smt_cert.has_side_effects = true;
        smt_cert.setCwd(b.path("."));
        smt_cert.addArgs(&.{ "check", "tests/cases/smt_cert.bpa" });
        smt_cert.expectStdErrEqual("");
        smt_cert.expectStdOutEqual("OK: 143 declarations, 40 theorems proven\n");
        smt_cert.expectExitCode(0);
        test_step.dependOn(&smt_cert.step);

        // mixed countermodel: arithmetic values plus opaque truth values
        const smt_bad = b.addRunArtifact(exe);
        smt_bad.has_side_effects = true;
        smt_bad.setCwd(b.path("."));
        smt_bad.addArgs(&.{ "check", "tests/cases/smt_bad.bpa" });
        smt_bad.expectStdErrEqual(
            "tests/cases/smt_bad.bpa:12:9: error: arithmetic: false at a := 0, p := false\n",
        );
        smt_bad.expectExitCode(1);
        test_step.dependOn(&smt_bad.step);

        // `define` abbreviations expand transparently; certificates unaffected
        const define_ok = b.addRunArtifact(exe);
        define_ok.has_side_effects = true;
        define_ok.setCwd(b.path("."));
        define_ok.addArgs(&.{ "check", "tests/cases/define.bpa" });
        define_ok.expectStdErrEqual("");
        define_ok.expectStdOutEqual("OK: 9 declarations, 1 theorems proven\n");
        define_ok.expectExitCode(0);
        test_step.dependOn(&define_ok.step);

        // defines share the declaration namespace
        const define_bad = b.addRunArtifact(exe);
        define_bad.has_side_effects = true;
        define_bad.setCwd(b.path("."));
        define_bad.addArgs(&.{ "check", "tests/cases/define_bad.bpa" });
        define_bad.expectStdErrEqual(
            "tests/cases/define_bad.bpa:5:8: error: duplicate declaration of 'TWO'\n",
        );
        define_bad.expectExitCode(1);
        test_step.dependOn(&define_bad.step);

        // the standard library must check
        const std_peano = b.addRunArtifact(exe);
        std_peano.has_side_effects = true;
        std_peano.setCwd(b.path("."));
        std_peano.addArgs(&.{ "check", "std/peano.bpa" });
        std_peano.expectStdErrEqual("");
        std_peano.expectStdOutEqual("OK: 48 declarations, 17 theorems proven\n");
        std_peano.expectExitCode(0);
        test_step.dependOn(&std_peano.step);

        // the standard library is oracle-free, forever
        const std_peano_pure = b.addRunArtifact(exe);
        std_peano_pure.has_side_effects = true;
        std_peano_pure.setCwd(b.path("."));
        std_peano_pure.addArgs(&.{ "check", "std/peano.bpa" });
        std_peano_pure.expectStdErrEqual("");
        std_peano_pure.expectStdOutEqual("OK: 48 declarations, 17 theorems proven\n");
        std_peano_pure.expectExitCode(0);
        test_step.dependOn(&std_peano_pure.step);

        // the order theory + strong induction, split into its own layer; pure,
        // and --recursive re-verifies the imported peano proofs too
        const std_ordering = b.addRunArtifact(exe);
        std_ordering.has_side_effects = true;
        std_ordering.setCwd(b.path("."));
        std_ordering.addArgs(&.{ "check", "std/peano-ordering.bpa" });
        std_ordering.expectStdErrEqual("");
        std_ordering.expectStdOutEqual("OK: 117 declarations, 38 theorems proven\n");
        std_ordering.expectExitCode(0);
        test_step.dependOn(&std_ordering.step);

        const std_ordering_rec = b.addRunArtifact(exe);
        std_ordering_rec.has_side_effects = true;
        std_ordering_rec.setCwd(b.path("."));
        std_ordering_rec.addArgs(&.{ "check", "std/peano-ordering.bpa" });
        std_ordering_rec.expectStdErrEqual("");
        std_ordering_rec.expectStdOutEqual("OK: 117 declarations, 38 theorems proven\n");
        std_ordering_rec.expectExitCode(0);
        test_step.dependOn(&std_ordering_rec.step);

        // truncated subtraction + the gcd measure lemma (Euclid foundation)
        const std_subtraction = b.addRunArtifact(exe);
        std_subtraction.has_side_effects = true;
        std_subtraction.setCwd(b.path("."));
        std_subtraction.addArgs(&.{ "check", "std/peano-subtraction.bpa" });
        std_subtraction.expectStdErrEqual("");
        std_subtraction.expectStdOutEqual("OK: 152 declarations, 44 theorems proven\n");
        std_subtraction.expectExitCode(0);
        test_step.dependOn(&std_subtraction.step);

        // divisibility + guarded Euclidean div/mod + the gcd bridge lemma
        const std_division = b.addRunArtifact(exe);
        std_division.has_side_effects = true;
        std_division.setCwd(b.path("."));
        std_division.addArgs(&.{ "check", "std/peano-division.bpa" });
        std_division.expectStdErrEqual("");
        std_division.expectStdOutEqual("OK: 204 declarations, 54 theorems proven\n");
        std_division.expectExitCode(0);
        test_step.dependOn(&std_division.step);

        // THE PAYOFF: Euclid's algorithm, proved correct (common divisor +
        // greatest), pure, by strong induction on the decreasing modulus
        const std_gcd = b.addRunArtifact(exe);
        std_gcd.has_side_effects = true;
        std_gcd.setCwd(b.path("."));
        std_gcd.addArgs(&.{ "check", "std/peano-gcd.bpa" });
        std_gcd.expectStdErrEqual("");
        std_gcd.expectStdOutEqual("OK: 227 declarations, 56 theorems proven\n");
        std_gcd.expectExitCode(0);
        test_step.dependOn(&std_gcd.step);

        // parity: even/odd + the crux 2|p² → 2|p, proved PURE (no oracle)
        const std_parity = b.addRunArtifact(exe);
        std_parity.has_side_effects = true;
        std_parity.setCwd(b.path("."));
        std_parity.addArgs(&.{ "check", "std/peano-parity.bpa" });
        std_parity.expectStdErrEqual("");
        std_parity.expectStdOutEqual("OK: 244 declarations, 59 theorems proven\n");
        std_parity.expectExitCode(0);
        test_step.dependOn(&std_parity.step);

        // instantiating strongInduction re-checks its full stored proof
        const strong_ind = b.addRunArtifact(exe);
        strong_ind.has_side_effects = true;
        strong_ind.setCwd(b.path("."));
        strong_ind.addArgs(&.{ "check", "tests/cases/strong_induction.bpa" });
        strong_ind.expectStdErrEqual("");
        strong_ind.expectStdOutEqual("OK: 125 declarations, 40 theorems proven\n");
        strong_ind.expectExitCode(0);
        test_step.dependOn(&strong_ind.step);

        // the outline fixture is itself a valid proof
        const outline_check = b.addRunArtifact(exe);
        outline_check.has_side_effects = true;
        outline_check.setCwd(b.path("."));
        outline_check.addArgs(&.{ "check", "tests/cases/outline.bpa" });
        outline_check.expectStdErrEqual("");
        outline_check.expectStdOutEqual("OK: 8 declarations, 1 theorems proven\n");
        outline_check.expectExitCode(0);
        test_step.dependOn(&outline_check.step);

        // `query outline <file> <theorem>`: the proof skeleton — bare labels,
        // with a header on each block opener (fix / assume / unpack / case).
        const outline_thm = b.addRunArtifact(exe);
        outline_thm.has_side_effects = true;
        outline_thm.setCwd(b.path("."));
        outline_thm.addArgs(&.{ "query", "outline", "tests/cases/outline.bpa", "everyoneIsQ" });
        outline_thm.expectStdErrEqual("");
        outline_thm.expectStdOutEqual(
            \\theorem everyoneIsQ
            \\  generalize-n  fix n
            \\    cases
            \\    p-or-q
            \\    conclusion-inner  case on p-or-q
            \\      from-p  assume p(n)
            \\        p-holds
            \\        p-gives-q
            \\        p-gives-q-at-n
            \\        q-from-p
            \\      from-q  assume q(n)
            \\        q-holds
            \\  conclusion
            \\
        );
        outline_thm.expectExitCode(0);
        test_step.dependOn(&outline_thm.step);

        // no theorem argument: outline every proof in the file (here, the one)
        const outline_all = b.addRunArtifact(exe);
        outline_all.has_side_effects = true;
        outline_all.setCwd(b.path("."));
        outline_all.addArgs(&.{ "query", "outline", "tests/cases/outline.bpa" });
        outline_all.expectStdErrEqual("");
        outline_all.expectStdOutEqual(
            \\theorem everyoneIsQ
            \\  generalize-n  fix n
            \\    cases
            \\    p-or-q
            \\    conclusion-inner  case on p-or-q
            \\      from-p  assume p(n)
            \\        p-holds
            \\        p-gives-q
            \\        p-gives-q-at-n
            \\        q-from-p
            \\      from-q  assume q(n)
            \\        q-holds
            \\  conclusion
            \\
        );
        outline_all.expectExitCode(0);
        test_step.dependOn(&outline_all.step);

        // a missing theorem is a located error on stderr (exit 1)
        const outline_missing = b.addRunArtifact(exe);
        outline_missing.has_side_effects = true;
        outline_missing.setCwd(b.path("."));
        outline_missing.addArgs(&.{ "query", "outline", "tests/cases/outline.bpa", "noSuchThing" });
        outline_missing.expectStdErrEqual("error: no theorem 'noSuchThing' in this file\n");
        outline_missing.expectExitCode(1);
        test_step.dependOn(&outline_missing.step);

        // `query uses <file>`: per-proof rule tally + external citations. The
        // refs that are the proof's OWN labels are excluded from `cites`; the
        // axioms/theorems it pulls in are listed.
        const q_uses = b.addRunArtifact(exe);
        q_uses.has_side_effects = true;
        q_uses.setCwd(b.path("."));
        q_uses.addArgs(&.{ "query", "uses", "tests/cases/outline.bpa" });
        q_uses.expectStdErrEqual("");
        q_uses.expectStdOutEqual("theorem everyoneIsQ\n" ++
            "  rules: axiom×2 forall_elim×2 hypothesis×2 modus_ponens forall_intro\n" ++
            "  cites: either pImpliesQ\n");
        q_uses.expectExitCode(0);
        test_step.dependOn(&q_uses.step);

        // `query oracles <file>`: a proof with no oracle-capable rule reports
        // pure.
        const q_oracles_pure = b.addRunArtifact(exe);
        q_oracles_pure.has_side_effects = true;
        q_oracles_pure.setCwd(b.path("."));
        q_oracles_pure.addArgs(&.{ "query", "oracles", "tests/cases/outline.bpa" });
        q_oracles_pure.expectStdErrEqual("");
        q_oracles_pure.expectStdOutEqual("no oracle-capable steps — this file's proofs are pure\n");
        q_oracles_pure.expectExitCode(0);
        test_step.dependOn(&q_oracles_pure.step);

        // `query oracles <file>`: oracle-capable steps flagged at file:line:col
        // with the rule name — here both `assoc_quantified` and `assoc` (the
        // quantified variant runs the same oracle-capable core).
        const q_oracles_hit = b.addRunArtifact(exe);
        q_oracles_hit.has_side_effects = true;
        q_oracles_hit.setCwd(b.path("."));
        q_oracles_hit.addArgs(&.{ "query", "oracles", "tests/cases/assoc.bpa" });
        q_oracles_hit.expectStdErrEqual("");
        q_oracles_hit.expectStdOutEqual("theorem reassoc1\n" ++
            "  tests/cases/assoc.bpa:19:9: assoc_quantified\n\n" ++
            "theorem reassoc2\n" ++
            "  tests/cases/assoc.bpa:28:9: assoc_quantified\n\n" ++
            "theorem reassoc3\n" ++
            "  tests/cases/assoc.bpa:45:25: assoc\n");
        q_oracles_hit.expectExitCode(0);
        test_step.dependOn(&q_oracles_hit.step);

        // `query theorem <file> <name>`: the full source of the declaration,
        // verbatim — leading doc-comment through `qed`. Pinned to real std
        // (brittle by design: a std edit to this theorem should break here).
        const std_theorem_text =
            \\// Strategy: induction on n with prop(k) := add(k, ZERO) = k.
            \\// (addZeroLeft reduces ZERO on the LEFT; this is the mirror-image fact.)
            \\theorem addZeroRight: forall n: Nat; add(n, ZERO) = n
            \\proof
            \\  // base case: addZeroLeft specialized at b := ZERO
            \\  @add-zero-left |
            \\    forall b: Nat; add(ZERO, b) = b
            \\    [by axiom addZeroLeft]
            \\  @base-case |
            \\    add(ZERO, ZERO) = ZERO
            \\    [by forall_elim(ZERO) add-zero-left]
            \\
            \\  // inductive step: unfold add on succ(k), then rewrite with the IH
            \\  @induction-step |
            \\    fix k: Nat {
            \\      @given-inductive-hypothesis |
            \\        assume add(k, ZERO) = k {
            \\          @add-succ-left |
            \\            forall a, b: Nat; add(succ(a), b) = succ(add(a, b))
            \\            [by axiom addSuccLeft]
            \\          @unfolded |
            \\            add(succ(k), ZERO) = succ(add(k, ZERO))
            \\            [by forall_elim(k, ZERO) add-succ-left]
            \\          @inductive-hypothesis |
            \\            add(k, ZERO) = k
            \\            [by hypothesis given-inductive-hypothesis]
            \\          @succ-case |
            \\            add(succ(k), ZERO) = succ(k)
            \\            [by rewrite inductive-hypothesis unfolded]
            \\        }
            \\      @induction-step-at-k |
            \\        add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
            \\        [by implies_intro given-inductive-hypothesis]
            \\    }
            \\  @induction-step-for-all-k |
            \\    forall k: Nat; add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
            \\    [by forall_intro induction-step]
            \\
            \\  @conclusion |
            \\    forall n: Nat; add(n, ZERO) = n
            \\    [by instantiate induction((fun k: Nat => add(k, ZERO) = k)) base-case induction-step-for-all-k]
            \\qed
            \\
        ;
        const q_thm = b.addRunArtifact(exe);
        q_thm.has_side_effects = true;
        q_thm.setCwd(b.path("."));
        q_thm.addArgs(&.{ "query", "theorem", "std/peano.bpa", "addZeroRight" });
        q_thm.expectStdErrEqual("");
        q_thm.expectStdOutEqual(std_theorem_text);
        q_thm.expectExitCode(0);
        test_step.dependOn(&q_thm.step);

        // an ALIAS (`theorem addZeroRight = peano.addZeroRight` in subtraction)
        // resolves across files to the real proof — identical output.
        const q_thm_alias = b.addRunArtifact(exe);
        q_thm_alias.has_side_effects = true;
        q_thm_alias.setCwd(b.path("."));
        q_thm_alias.addArgs(&.{ "query", "theorem", "std/peano-subtraction.bpa", "addZeroRight" });
        q_thm_alias.expectStdErrEqual("");
        q_thm_alias.expectStdOutEqual(std_theorem_text);
        q_thm_alias.expectExitCode(0);
        test_step.dependOn(&q_thm_alias.step);

        // a missing theorem: located error, exit 1
        const q_thm_missing = b.addRunArtifact(exe);
        q_thm_missing.has_side_effects = true;
        q_thm_missing.setCwd(b.path("."));
        q_thm_missing.addArgs(&.{ "query", "theorem", "std/peano.bpa", "noSuchThing" });
        q_thm_missing.expectStdErrEqual("error: no theorem 'noSuchThing' in this file\n");
        q_thm_missing.expectExitCode(1);
        test_step.dependOn(&q_thm_missing.step);

        // `--sig`: just the statement, wrap-collapsed to one line, alias-
        // followed. `induction` wraps across two lines in the source.
        const q_thm_sig = b.addRunArtifact(exe);
        q_thm_sig.has_side_effects = true;
        q_thm_sig.setCwd(b.path("."));
        q_thm_sig.addArgs(&.{ "query", "theorem", "std/peano.bpa", "induction", "--sig" });
        q_thm_sig.expectStdErrEqual("");
        q_thm_sig.expectStdOutEqual("axiom induction(prop: Nat -> Prop): prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)\n");
        q_thm_sig.expectExitCode(0);
        test_step.dependOn(&q_thm_sig.step);

        // `query whereis <file> <ident>`: trace an alias across files to its
        // origin. Pinned to real std (brittle by design). `sub` is a func
        // aliased in parity from subtraction.
        const q_whereis = b.addRunArtifact(exe);
        q_whereis.has_side_effects = true;
        q_whereis.setCwd(b.path("."));
        q_whereis.addArgs(&.{ "query", "whereis", "std/peano-parity.bpa", "sub" });
        q_whereis.expectStdErrEqual("");
        q_whereis.expectStdOutEqual(
            \\sub
            \\  std/peano-parity.bpa:19:  func sub = subtraction.sub
            \\  std/peano-subtraction.bpa:38:  func sub(a: Nat, b: Nat): Nat  [origin]
            \\
        );
        q_whereis.expectExitCode(0);
        test_step.dependOn(&q_whereis.step);

        // an import namespace resolves to the imported file as its origin.
        const q_whereis_ns = b.addRunArtifact(exe);
        q_whereis_ns.has_side_effects = true;
        q_whereis_ns.setCwd(b.path("."));
        q_whereis_ns.addArgs(&.{ "query", "whereis", "std/peano-parity.bpa", "division" });
        q_whereis_ns.expectStdErrEqual("");
        q_whereis_ns.expectStdOutEqual(
            \\division
            \\  std/peano-parity.bpa:10:  import division <<< "std/peano-division.bpa"
            \\  std/peano-division.bpa  [origin: imported file]
            \\
        );
        q_whereis_ns.expectExitCode(0);
        test_step.dependOn(&q_whereis_ns.step);

        // an unknown identifier: located error, exit 1
        const q_whereis_missing = b.addRunArtifact(exe);
        q_whereis_missing.has_side_effects = true;
        q_whereis_missing.setCwd(b.path("."));
        q_whereis_missing.addArgs(&.{ "query", "whereis", "std/peano.bpa", "noSuchName" });
        q_whereis_missing.expectStdErrEqual("noSuchName\n  error: no declaration named 'noSuchName' in std/peano.bpa\n");
        q_whereis_missing.expectExitCode(1);
        test_step.dependOn(&q_whereis_missing.step);

        // the search fixture is itself a valid proof
        const search_check = b.addRunArtifact(exe);
        search_check.has_side_effects = true;
        search_check.setCwd(b.path("."));
        search_check.addArgs(&.{ "check", "tests/cases/search_target.bpa" });
        search_check.expectStdErrEqual("");
        search_check.expectStdOutEqual("OK: 8 declarations, 1 theorems proven\n");
        search_check.expectExitCode(0);
        test_step.dependOn(&search_check.step);

        // `query search <file> <query>`: fuzzy match over theorem/axiom names +
        // statements. Both "cancel"-named decls match; ranked, one-line sigs.
        const q_search = b.addRunArtifact(exe);
        q_search.has_side_effects = true;
        q_search.setCwd(b.path("."));
        q_search.addArgs(&.{ "query", "search", "tests/cases/search_target.bpa", "cancel" });
        q_search.expectStdErrEqual("");
        q_search.expectStdOutEqual(
            \\tests/cases/search_target.bpa:13:  axiom cancelAxiom: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
            \\tests/cases/search_target.bpa:16:  theorem addCancelLeft: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
            \\
        );
        q_search.expectExitCode(0);
        test_step.dependOn(&q_search.step);

        // no match: message + exit 1
        const q_search_miss = b.addRunArtifact(exe);
        q_search_miss.has_side_effects = true;
        q_search_miss.setCwd(b.path("."));
        q_search_miss.addArgs(&.{ "query", "search", "tests/cases/search_target.bpa", "zzznope" });
        q_search_miss.expectStdErrEqual("no theorem or axiom matching 'zzznope'\n");
        q_search_miss.expectExitCode(1);
        test_step.dependOn(&q_search_miss.step);

        // directory boundaries: subdir import chaining to a parent-dir import
        const imp_chain = b.addRunArtifact(exe);
        imp_chain.has_side_effects = true;
        imp_chain.setCwd(b.path("."));
        imp_chain.addArgs(&.{ "check", "tests/cases/imports/chain.bpa" });
        imp_chain.expectStdErrEqual("");
        imp_chain.expectExitCode(0);
        test_step.dependOn(&imp_chain.step);

        // diamond imports + re-export: one lib, two hops, same entities
        const imp_diamond = b.addRunArtifact(exe);
        imp_diamond.has_side_effects = true;
        imp_diamond.setCwd(b.path("."));
        imp_diamond.addArgs(&.{ "check", "tests/cases/imports/diamond.bpa" });
        imp_diamond.expectStdErrEqual("");
        imp_diamond.expectExitCode(0);
        test_step.dependOn(&imp_diamond.step);

        // guards travel across imports
        const imp_guarded = b.addRunArtifact(exe);
        imp_guarded.has_side_effects = true;
        imp_guarded.setCwd(b.path("."));
        imp_guarded.addArgs(&.{ "check", "tests/cases/imports/guarded_bad.bpa" });
        imp_guarded.expectStdErrEqual(
            "tests/cases/imports/guarded_bad.bpa:4:14: error: unproved obligation: 'Z != Z'\n",
        );
        imp_guarded.expectExitCode(1);
        test_step.dependOn(&imp_guarded.step);

        // a missing import file is a clean diagnostic at the import site
        const imp_missing = b.addRunArtifact(exe);
        imp_missing.has_side_effects = true;
        imp_missing.setCwd(b.path("."));
        imp_missing.addArgs(&.{ "check", "tests/cases/imports/missing_import.bpa" });
        imp_missing.expectStdErrEqual(
            "tests/cases/imports/missing_import.bpa:2:18: error: cannot open 'tests/cases/imports/nope.bpa': file not found\n",
        );
        imp_missing.expectExitCode(1);
        test_step.dependOn(&imp_missing.step);

        // a namespace name collides with a local declaration
        const imp_collide = b.addRunArtifact(exe);
        imp_collide.has_side_effects = true;
        imp_collide.setCwd(b.path("."));
        imp_collide.addArgs(&.{ "check", "tests/cases/imports/collide.bpa" });
        imp_collide.expectStdErrEqual(
            "tests/cases/imports/collide.bpa:3:8: error: duplicate declaration of 'lib'\n",
        );
        imp_collide.expectExitCode(1);
        test_step.dependOn(&imp_collide.step);

        // Gauss's summation formula, by hand, proved pure over the imported base
        const gauss = b.addRunArtifact(exe);
        gauss.has_side_effects = true;
        gauss.setCwd(b.path("."));
        gauss.addArgs(&.{ "check", "examples/gauss-pure.bpa" });
        gauss.expectStdErrEqual("");
        gauss.expectStdOutEqual("OK: 70 declarations, 19 theorems proven\n");
        gauss.expectExitCode(0);
        test_step.dependOn(&gauss.step);

        // the automation-assisted twin: `ac` replaces the by-hand exchange
        // lemma, still pure
        const gauss_ac = b.addRunArtifact(exe);
        gauss_ac.has_side_effects = true;
        gauss_ac.setCwd(b.path("."));
        gauss_ac.addArgs(&.{ "check", "examples/gauss.bpa" });
        gauss_ac.expectStdErrEqual("");
        gauss_ac.expectStdOutEqual("OK: 70 declarations, 18 theorems proven\n");
        gauss_ac.expectExitCode(0);
        test_step.dependOn(&gauss_ac.step);

        // Euclid's algorithm from a consumer's view: import the verified gcd
        // library and cite its correctness theorems to derive concrete facts
        const euclid = b.addRunArtifact(exe);
        euclid.has_side_effects = true;
        euclid.setCwd(b.path("."));
        euclid.addArgs(&.{ "check", "examples/euclid.bpa" });
        euclid.expectStdErrEqual("");
        euclid.expectStdOutEqual("OK: 236 declarations, 59 theorems proven\n");
        euclid.expectExitCode(0);
        test_step.dependOn(&euclid.step);

        const euclid_compute = b.addRunArtifact(exe);
        euclid_compute.has_side_effects = true;
        euclid_compute.setCwd(b.path("."));
        euclid_compute.addArgs(&.{ "check", "examples/euclid-compute.bpa" });
        euclid_compute.expectStdErrEqual("");
        euclid_compute.expectStdOutEqual("OK: 259 declarations, 61 theorems proven\n");
        euclid_compute.expectExitCode(0);
        test_step.dependOn(&euclid_compute.step);

        // √2 is irrational (stated over ℕ), proved PURE — the headline result.
        const sqrt2 = b.addRunArtifact(exe);
        sqrt2.has_side_effects = true;
        sqrt2.setCwd(b.path("."));
        sqrt2.addArgs(&.{ "check", "examples/sqrt2.bpa" });
        sqrt2.expectStdErrEqual("");
        sqrt2.expectStdOutEqual("OK: 291 declarations, 62 theorems proven\n");
        sqrt2.expectExitCode(0);
        test_step.dependOn(&sqrt2.step);

        // literate: `check` on a .md checks its ```bpa blocks (prose masked).
        const literate = b.addRunArtifact(exe);
        literate.has_side_effects = true;
        literate.setCwd(b.path("."));
        literate.addArgs(&.{ "check", "examples/literate.md" });
        literate.expectStdErrEqual("");
        literate.expectStdOutEqual("OK: 6 declarations, 1 theorems proven\n");
        literate.expectExitCode(0);
        test_step.dependOn(&literate.step);

        // an error in an embedded proof maps to the .md's OWN line number
        // (prose-masking preserves line offsets).
        const literate_bad = b.addRunArtifact(exe);
        literate_bad.has_side_effects = true;
        literate_bad.setCwd(b.path("."));
        literate_bad.addArgs(&.{ "check", "tests/cases/literate_bad.md" });
        literate_bad.expectStdErrEqual("tests/cases/literate_bad.md:16:4: error: reflexivity requires a claim of the form 't = t', got 'A = B'\n");
        literate_bad.expectExitCode(1);
        test_step.dependOn(&literate_bad.step);

        // the group theory (std/group.bpa): axioms only, no theorems — so a
        // direct check materializes nothing and exits nonzero with a warning
        // (the theory is a valid dependency, but checking it alone proves 0).
        const std_group = b.addRunArtifact(exe);
        std_group.has_side_effects = true;
        std_group.setCwd(b.path("."));
        std_group.addArgs(&.{ "check", "std/group.bpa" });
        std_group.expectStdErrEqual("");
        // exit-code check MUST precede expectStdOutEqual: the latter auto-adds
        // an `exited=0` term check when none exists yet, which would conflict.
        std_group.expectExitCode(1);
        std_group.expectStdOutEqual("OK: 9 declarations, 0 theorems proven\n" ++
            "  \u{2014} WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).\n");
        test_step.dependOn(&std_group.step);

        // AATA group theory: the literate translation of Groups basic-
        // properties (5 propositions) + 5 in-scope exercises, verified PURE.
        const aata_groups = b.addRunArtifact(exe);
        aata_groups.has_side_effects = true;
        aata_groups.setCwd(b.path("."));
        aata_groups.addArgs(&.{ "check", "aata/groups.md" });
        aata_groups.expectStdErrEqual("");
        aata_groups.expectStdOutEqual("OK: 29 declarations, 10 theorems proven\n");
        aata_groups.expectExitCode(0);
        test_step.dependOn(&aata_groups.step);

        // the set theory (std/set.bpa): axioms only, no theorems — a direct
        // check materializes nothing and exits nonzero with a warning.
        const std_set = b.addRunArtifact(exe);
        std_set.has_side_effects = true;
        std_set.setCwd(b.path("."));
        std_set.addArgs(&.{ "check", "std/set.bpa" });
        std_set.expectStdErrEqual("");
        std_set.expectExitCode(1);
        std_set.expectStdOutEqual("OK: 14 declarations, 0 theorems proven\n" ++
            "  \u{2014} WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).\n");
        test_step.dependOn(&std_set.step);

        // AATA set theory: the literate transliteration of Chapter 1 §1.2.1
        // (the set-algebra proposition + De Morgan's laws), verified PURE.
        const aata_sets = b.addRunArtifact(exe);
        aata_sets.has_side_effects = true;
        aata_sets.setCwd(b.path("."));
        aata_sets.addArgs(&.{ "check", "aata/sets.md" });
        aata_sets.expectStdErrEqual("");
        aata_sets.expectStdOutEqual("OK: 43 declarations, 14 theorems proven\n");
        aata_sets.expectExitCode(0);
        test_step.dependOn(&aata_sets.step);

        // the function theory (std/function.bpa): axioms only, no theorems — a
        // direct check materializes nothing and exits nonzero with a warning.
        const std_function = b.addRunArtifact(exe);
        std_function.has_side_effects = true;
        std_function.setCwd(b.path("."));
        std_function.addArgs(&.{ "check", "std/function.bpa" });
        std_function.expectStdErrEqual("");
        std_function.expectExitCode(1);
        std_function.expectStdOutEqual("OK: 14 declarations, 0 theorems proven\n" ++
            "  \u{2014} WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).\n");
        test_step.dependOn(&std_function.step);

        // AATA functions: the literate transliteration of Chapter 1 §1.2.2
        // (composition associativity/preservation + invertible⇒bijective
        // forward), verified PURE. The backward direction is a marked wall.
        const aata_functions = b.addRunArtifact(exe);
        aata_functions.has_side_effects = true;
        aata_functions.setCwd(b.path("."));
        aata_functions.addArgs(&.{ "check", "aata/functions.md" });
        aata_functions.expectStdErrEqual("");
        aata_functions.expectStdOutEqual("OK: 36 declarations, 7 theorems proven\n");
        aata_functions.expectExitCode(0);
        test_step.dependOn(&aata_functions.step);

        // --faster trusts imported proofs (peano-imports imports peano.bpa,
        // whose one oracle step would otherwise be re-checked and hard-error).
        const imp_demo = b.addRunArtifact(exe);
        imp_demo.has_side_effects = true;
        imp_demo.setCwd(b.path("."));
        imp_demo.addArgs(&.{ "check", "--faster", "examples/peano-imports.bpa" });
        imp_demo.expectStdErrEqual("");
        imp_demo.expectStdOutEqual("OK: 24 declarations, 1 theorems proven, 6 imported theorems trusted\n" ++
            "  \u{2014} NOT FULLY VERIFIED (deferred: arithmetic-certificates imported-proofs); re-run `bpa check` before finalizing.\n");
        imp_demo.expectExitCode(0);
        test_step.dependOn(&imp_demo.step);

        // --fast re-checks the imported proofs but accepts the imported oracle
        const imp_demo_fast = b.addRunArtifact(exe);
        imp_demo_fast.has_side_effects = true;
        imp_demo_fast.setCwd(b.path("."));
        imp_demo_fast.addArgs(&.{ "check", "--fast", "examples/peano-imports.bpa" });
        imp_demo_fast.expectStdErrEqual("");
        imp_demo_fast.expectStdOutEqual("OK: 24 declarations, 7 theorems proven (6 pure, 1 via oracles: arithmetic)\n" ++
            "  \u{2014} NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.\n");
        imp_demo_fast.expectExitCode(0);
        test_step.dependOn(&imp_demo_fast.step);

        // trust semantics: importing an INCORRECT theorem passes under --faster
        // (imported proofs trusted)...
        const trusts = b.addRunArtifact(exe);
        trusts.has_side_effects = true;
        trusts.setCwd(b.path("."));
        trusts.addArgs(&.{ "check", "--faster", "tests/cases/imports/trusts_broken.bpa" });
        trusts.expectStdErrEqual("");
        trusts.expectStdOutEqual("OK: 7 declarations, 1 theorems proven, 1 imported theorems trusted\n" ++
            "  \u{2014} NOT FULLY VERIFIED (deferred: arithmetic-certificates imported-proofs); re-run `bpa check` before finalizing.\n");
        trusts.expectExitCode(0);
        test_step.dependOn(&trusts.step);

        // ...and is caught by the DEFAULT (imported proofs re-checked),
        // poisoning its citations downstream
        const trusts_rec = b.addRunArtifact(exe);
        trusts_rec.has_side_effects = true;
        trusts_rec.setCwd(b.path("."));
        trusts_rec.addArgs(&.{ "check", "tests/cases/imports/trusts_broken.bpa" });
        trusts_rec.expectStdErrEqual(
            "tests/cases/imports/trusts_broken.bpa:8:17: error: cites unproven theorem 'aIsB'\n" ++
                "tests/cases/imports/broken_lib.bpa:9:4: error: proof concludes 'A = A' but the theorem states 'A = B'\n",
        );
        trusts_rec.expectExitCode(1);
        test_step.dependOn(&trusts_rec.step);

        // --reckless additionally trusts imported schemas (banner names all
        // three deferred layers)
        const reckless = b.addRunArtifact(exe);
        reckless.has_side_effects = true;
        reckless.setCwd(b.path("."));
        reckless.addArgs(&.{ "check", "--reckless", "examples/peano-imports.bpa" });
        reckless.expectStdErrEqual("");
        reckless.expectStdOutEqual("OK: 24 declarations, 1 theorems proven, 6 imported theorems trusted\n" ++
            "  \u{2014} NOT FULLY VERIFIED (deferred: arithmetic-certificates imported-proofs imported-schemas); re-run `bpa check` before finalizing.\n");
        reckless.expectExitCode(0);
        test_step.dependOn(&reckless.step);

        // at most one speed flag
        const two_flags = b.addRunArtifact(exe);
        two_flags.has_side_effects = true;
        two_flags.setCwd(b.path("."));
        two_flags.addArgs(&.{ "check", "--fast", "--reckless", "examples/peano-imports.bpa" });
        two_flags.expectStdErrEqual("error: at most one of --fast / --faster / --reckless\n");
        two_flags.expectExitCode(1);
        test_step.dependOn(&two_flags.step);

        const imp_uses = b.addRunArtifact(exe);
        imp_uses.has_side_effects = true;
        imp_uses.setCwd(b.path("."));
        imp_uses.addArgs(&.{ "check", "tests/cases/imports/uses.bpa" });
        imp_uses.expectStdErrEqual("");
        imp_uses.expectExitCode(0);
        test_step.dependOn(&imp_uses.step);

        // Imports, broken siblings (messages pinned once implemented)
        const imp_cycle = b.addRunArtifact(exe);
        imp_cycle.has_side_effects = true;
        imp_cycle.setCwd(b.path("."));
        imp_cycle.addArgs(&.{ "check", "tests/cases/imports/cycle_a.bpa" });
        imp_cycle.expectStdErrEqual(
            "tests/cases/imports/cycle_b.bpa:2:14: error: import cycle detected via 'tests/cases/imports/cycle_a.bpa'\n",
        );
        imp_cycle.expectExitCode(1);
        test_step.dependOn(&imp_cycle.step);

        const imp_bad_alias = b.addRunArtifact(exe);
        imp_bad_alias.has_side_effects = true;
        imp_bad_alias.setCwd(b.path("."));
        imp_bad_alias.addArgs(&.{ "check", "tests/cases/imports/bad_alias.bpa" });
        imp_bad_alias.expectStdErrEqual(
            "tests/cases/imports/bad_alias.bpa:3:14: error: 'lib.NIL' is not a sort\n",
        );
        imp_bad_alias.expectExitCode(1);
        test_step.dependOn(&imp_bad_alias.step);

        const imp_unknown_ns = b.addRunArtifact(exe);
        imp_unknown_ns.has_side_effects = true;
        imp_unknown_ns.setCwd(b.path("."));
        imp_unknown_ns.addArgs(&.{ "check", "tests/cases/imports/unknown_ns.bpa" });
        imp_unknown_ns.expectStdErrEqual(
            "tests/cases/imports/unknown_ns.bpa:3:10: error: unknown namespace 'ghost'\n",
        );
        imp_unknown_ns.expectExitCode(1);
        test_step.dependOn(&imp_unknown_ns.step);

        // M5: guards discharged by hypothesis and by matching lemma
        const div_ok = b.addRunArtifact(exe);
        div_ok.has_side_effects = true;
        div_ok.setCwd(b.path("."));
        div_ok.addArgs(&.{ "check", "tests/cases/div_ok.bpa" });
        div_ok.expectStdErrEqual("");
        div_ok.expectExitCode(0);
        test_step.dependOn(&div_ok.step);

        // M5: unguarded division is rejected with the exact obligation
        const div_bad = b.addRunArtifact(exe);
        div_bad.has_side_effects = true;
        div_bad.setCwd(b.path("."));
        div_bad.addArgs(&.{ "check", "tests/cases/div_bad.bpa" });
        div_bad.expectStdErrEqual(
            "tests/cases/div_bad.bpa:7:14: error: unproved obligation: 'ZERO != ZERO'\n" ++
                "tests/cases/div_bad.bpa:7:31: error: unproved obligation: 'ZERO != ZERO'\n",
        );
        div_bad.expectExitCode(1);
        test_step.dependOn(&div_bad.step);

        // M5: nested guarded applications report every obligation
        const div_nested = b.addRunArtifact(exe);
        div_nested.has_side_effects = true;
        div_nested.setCwd(b.path("."));
        div_nested.addArgs(&.{ "check", "tests/cases/div_nested.bpa" });
        div_nested.expectStdErrEqual(
            "tests/cases/div_nested.bpa:6:16: error: unproved obligation: 'div(ZERO, ZERO) != ZERO'\n" ++
                "tests/cases/div_nested.bpa:6:26: error: unproved obligation: 'ZERO != ZERO'\n",
        );
        div_nested.expectExitCode(1);
        test_step.dependOn(&div_nested.step);

        // Review fix: not_intro may only cite steps available at the END of
        // the cited subproof, not inside deeper nested assumptions
        const ni_bad = b.addRunArtifact(exe);
        ni_bad.has_side_effects = true;
        ni_bad.setCwd(b.path("."));
        ni_bad.addArgs(&.{ "check", "tests/cases/not_intro_nested_bad.bpa" });
        ni_bad.expectStdErrEqual(
            "tests/cases/not_intro_nested_bad.bpa:24:21: error: not_intro: 's1' is not accessible at the conclusion of the cited subproof\n",
        );
        ni_bad.expectExitCode(1);
        test_step.dependOn(&ni_bad.step);

        // Review fix: a block whose only content is a nested subproof has no
        // conclusion to discharge (was: kernel panic)
        const nc_bad = b.addRunArtifact(exe);
        nc_bad.has_side_effects = true;
        nc_bad.setCwd(b.path("."));
        nc_bad.addArgs(&.{ "check", "tests/cases/no_conclusion_bad.bpa" });
        nc_bad.expectStdErrEqual(
            "tests/cases/no_conclusion_bad.bpa:18:23: error: subproof 'b' has no concluding step of its own\n",
        );
        nc_bad.expectExitCode(1);
        test_step.dependOn(&nc_bad.step);
    }
}
