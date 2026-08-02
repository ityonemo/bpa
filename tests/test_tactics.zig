//! Integration gates — the automation tactics and their fixtures: simplify, ac / assoc / distribute, polynomial, tautology, arithmetic / Presburger, Farkas, and their `_bad` diagnostics.
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
    // Milestone A: simplify — certificate-producing rewrite tactic
    ctx.ok(&.{ "check", "tests/cases/simplify.bpa" }, "OK: 13 declarations, 2 theorems proven\n");

    // simplify is elaborated (never an accelerated tactic): the default check accepts it
    ctx.ok(&.{ "check", "tests/cases/simplify.bpa" }, "OK: 13 declarations, 2 theorems proven\n");

    // unjoinable normal forms: the diagnostic shows both, copy-pasteable
    ctx.fail(&.{ "check", "tests/cases/simplify_bad.bpa" }, "tests/cases/simplify_bad.bpa:14:13: error: simplify: normal forms differ: 'add(n, ZERO)' vs 'n'\n");

    // cycling rules hit the hard rewrite cap instead of hanging
    ctx.fail(&.{ "check", "tests/cases/simplify_loop.bpa" }, "tests/cases/simplify_loop.bpa:13:9: error: simplify: rewrite limit reached (looping rule set?)\n");

    // ac: associative-commutative sum reordering over opaque atoms, elaborated
    ctx.ok(&.{ "check", "tests/cases/ac.bpa" }, "OK: 59 declarations, 19 theorems proven\n");

    // ac over multiplication: same bubble-sort machinery, mul lemma triple
    // (mulIsAssociative/mulIsCommutative/mulLeftSwap), elaborated
    ctx.ok(&.{ "check", "tests/cases/ac_mul.bpa" }, "OK: 59 declarations, 18 theorems proven\n");

    // ac_quantified: peel the forall prefix then run the ac core (add + mul)
    ctx.ok(&.{ "check", "tests/cases/ac_quantified.bpa" }, "OK: 60 declarations, 19 theorems proven\n");

    // distributivity: ac_quantified with a cited distributivity lemma
    // pre-normalizes (distributes) each side before the AC bubble-sort
    ctx.ok(&.{ "check", "tests/cases/distribute.bpa" }, "OK: 57 declarations, 18 theorems proven\n");

    // `polynomial(theory)`: nonlinear identities canonicalize elaborated (no
    // accelerated tactic) via distribute → sort monomials → sort sum → fold.
    ctx.ok(&.{ "check", "tests/cases/polynomial.bpa" }, "OK: 54 declarations, 19 theorems proven\n");

    // sides with different expansions → located error, exit 1 (not accelerated)
    ctx.fail(&.{ "check", "tests/cases/polynomial_bad.bpa" }, "tests/cases/polynomial_bad.bpa:18:9: error: polynomial: sides expand differently: 'add(mul(poly, poly), add(mul(poly, poly), add(mul(poly, poly), mul(poly, poly))))' vs 'add(mul(poly, poly), mul(poly, poly))'\n");

    // the polynomial ACCELERATED TACTIC: a thin theory (no ring lemmas) DECLINES under
    // the default (needs a lemma), but --fast decides it structurally and
    // is accelerated (accelerated: polynomial).
    ctx.fail(&.{ "check", "tests/cases/polynomial_oracle.bpa" }, "tests/cases/polynomial_oracle.bpa:22:9: error: polynomial: needs mulAddDistribLeft in scope\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oracle.bpa" },
        \\OK: 6 declarations, 1 theorems proven (0 elaborated, 1 accelerated: polynomial)
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );

    // Regression: the lemma-free accelerated tactic normalizer distributes a wide-sum 4th
    // power (256 monomials); building each product reallocates the term pool,
    // which pool.args aliases — the old code read a dangling arg slice and
    // panicked. Must check clean under --fast (never crash).
    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oob.bpa" },
        \\OK: 6 declarations, 1 theorems proven (0 elaborated, 1 accelerated: polynomial)
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );

    // ac on different multisets reports the mismatch (elaborated, not accelerated)
    ctx.fail(&.{ "check", "tests/cases/ac_bad.bpa" }, "tests/cases/ac_bad.bpa:18:17: error: assoc_commut: sides have different summands: 'add(b, add(a, a))' vs 'add(b, a)'\n");

    // assoc_commut(assoc, comm, swap): the explicit-triple form on a CUSTOM
    // operator (elaborated — the triple is kernel-checked).
    ctx.ok(&.{ "check", "tests/cases/assoc_commut_custom.bpa" }, "OK: 7 declarations, 2 theorems proven\n");

    // no partials: 1 or 2 args is an error (either bare or exactly three).
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_bad_arity.bpa" }, "tests/cases/assoc_commut_bad_arity.bpa:12:9: error: assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got 2\n");

    // the assoc_commut ACCELERATED TACTIC: bare form on a thin theory (no AC lemmas)
    // DECLINES by default, but --fast decides structurally and is accelerated.
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_oracle.bpa" }, "tests/cases/assoc_commut_oracle.bpa:16:9: error: assoc_commut: needs addIsAssociative in scope\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/assoc_commut_oracle.bpa" },
        \\OK: 4 declarations, 1 theorems proven (0 elaborated, 1 accelerated: assoc_commut)
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );

    // `assoc(assocLemma)`: associativity-only reorder on a CUSTOM operator
    // (no add/mul assumption). Elaborated.
    ctx.ok(&.{ "check", "tests/cases/assoc.bpa" }, "OK: 6 declarations, 3 theorems proven\n");

    // sides differ by more than associativity (operands permuted) → error
    ctx.fail(&.{ "check", "tests/cases/assoc_bad.bpa" }, "tests/cases/assoc_bad.bpa:11:9: error: assoc: sides differ by more than associativity: 'op(assoc, assoc)' vs 'op(assoc, assoc)'\n");

    // the required-arg contract: bare `assoc` is an error
    ctx.fail(&.{ "check", "tests/cases/assoc_missing_arg.bpa" }, "tests/cases/assoc_missing_arg.bpa:10:9: error: assoc requires an associativity lemma: assoc(<assocLemma>); got 0 argument(s)\n");

    // the assoc ACCELERATED TACTIC: certifies by default, --fast is accelerated
    ctx.ok(&.{ "check", "tests/cases/assoc_oracle.bpa" }, "OK: 4 declarations, 1 theorems proven\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/assoc_oracle.bpa" },
        \\OK: 4 declarations, 1 theorems proven (0 elaborated, 1 accelerated: assoc)
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );

    // simplify_quantified: peel forall over an equation, elaborated
    ctx.ok(&.{ "check", "tests/cases/simplify_quantified.bpa" }, "OK: 8 declarations, 2 theorems proven\n");

    // simplify_quantified on a bare equation redirects to simplify
    ctx.fail(&.{ "check", "tests/cases/simplify_quantified_bad.bpa" }, "tests/cases/simplify_quantified_bad.bpa:12:9: error: simplify_quantified expects a quantified goal; did you mean simplify?\n");

    // plain simplify on a quantified goal redirects to simplify_quantified
    ctx.fail(&.{ "check", "tests/cases/simplify_on_quantified.bpa" }, "tests/cases/simplify_on_quantified.bpa:12:9: error: simplify proves equations; did you mean simplify_quantified?\n");

    // symmetry: y = x from x = y in one step, elaborated
    ctx.ok(&.{ "check", "tests/cases/symmetry.bpa" }, "OK: 6 declarations, 1 theorems proven\n");

    // Milestone B2: tautology emits certificates — kernel-checked steps,
    // elaborated, not accelerated (the accelerated path remains as the over-budget fallback)
    ctx.ok(&.{ "check", "tests/cases/tautology.bpa" }, "OK: 9 declarations, 5 theorems proven\n");

    // certificates check elaborated by default (no accelerated tactic)
    ctx.ok(&.{ "check", "tests/cases/tautology.bpa" }, "OK: 9 declarations, 5 theorems proven\n");

    // non-consequence: the diagnostic carries the countermodel
    ctx.fail(&.{ "check", "tests/cases/tautology_bad.bpa" }, "tests/cases/tautology_bad.bpa:10:9: error: tautology: not a propositional consequence; countermodel: p := true, q := false\n");

    // the atom cap is a hard, honest limit
    ctx.fail(&.{ "check", "tests/cases/tautology_cap.bpa" }, "tests/cases/tautology_cap.bpa:25:9: error: tautology: 17 distinct atoms exceeds the limit of 16\n");

    // Milestone C: arithmetic accelerated tactic — Presburger quantifier elimination
    ctx.ok(&.{ "check", "--fast", "tests/cases/arithmetic.bpa" },
        \\OK: 9 declarations, 4 theorems proven (0 elaborated, 4 accelerated: arithmetic)
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );

    // false statement: the diagnostic carries countermodel values
    ctx.fail(&.{ "check", "tests/cases/arithmetic_bad.bpa" }, "tests/cases/arithmetic_bad.bpa:17:17: error: arithmetic: false at a := 0, b := 0\n");

    // a relation opaque only because it hides a nonlinear term is
    // reported honestly as outside the fragment, not as a false countermodel
    ctx.fail(&.{ "check", "tests/cases/arithmetic_frag.bpa" }, "tests/cases/arithmetic_frag.bpa:15:9: error: arithmetic: 'mul(a, b)' is outside linear arithmetic\n");

    // Milestone D: the SMT combination — mixed goals, one accelerated-tactic name
    ctx.ok(&.{ "check", "--fast", "tests/cases/smt.bpa" },
        \\OK: 9 declarations, 2 theorems proven (0 elaborated, 2 accelerated: arithmetic)
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );

    // Milestone C2b: universal linear goals replay as elaborated certificates
    // (sorted-sum normalization + synthesized order witnesses)
    ctx.ok(&.{ "check", "tests/cases/arithmetic_cert2.bpa" }, "OK: 146 declarations, 44 theorems proven\n");

    // Farkas: difference-logic infeasibility (combine several order
    // hypotheses into a transitivity cycle) certifies purely under the
    // DEFAULT, via `arithmetic(<theory>)` resolving the order lemmas
    // against the named module — no local aliasing of the vocabulary.
    ctx.ok(&.{ "check", "tests/cases/farkas.bpa" }, "OK: 122 declarations, 40 theorems proven\n");

    // Farkas extensions: order composition (a<b -> b<c -> a<c, no cycle)
    // and the infeasibility cap (contradictory order hyps prove an
    // arbitrary conclusion via lessThanIrreflexive + absurd).
    ctx.ok(&.{ "check", "tests/cases/farkas_ext.bpa" }, "OK: 124 declarations, 41 theorems proven\n");

    // Farkas coefficient scaling (stage 1): a hypothesis scaled by a literal
    // via multiplicationPreservesOrder before the infeasibility fold.
    ctx.ok(&.{ "check", "tests/cases/farkas_scale.bpa" }, "OK: 125 declarations, 39 theorems proven\n");

    // Farkas sum path (stage 2): sum two order hypotheses over distinct
    // variables via additionPreservesOrder + commutativity + transitivity.
    ctx.ok(&.{ "check", "tests/cases/farkas_sum.bpa" }, "OK: 122 declarations, 39 theorems proven\n");

    // Milestone C2a: ground goals replay as elaborated simplify certificates
    // over the well-known peano axioms — the default check accepts them
    ctx.ok(&.{ "check", "tests/cases/arithmetic_cert.bpa" }, "OK: 13 declarations, 2 theorems proven\n");

    // Cooper-replay layer 2 (witness direction): a `forall x; exists y; …`
    // goal with a period-1 Cooper trace elaborates fully — the cooper link
    // picks a boundary witness and emits exists_intro over an or-intro arm.
    ctx.ok(&.{ "check", "tests/cases/cooper_witness.bpa" }, "OK: 12 declarations, 1 theorems proven\n");

    // Cooper-replay layer 3 (periodicity direction): a period-2 (parity) ∀∃
    // goal elaborates fully via a SYNTHESIZED induction — the cooper link builds
    // predicate P(k), proves base P(ZERO) and step P(k)->P(succ(k)) (unpacking
    // the IH witness and shifting it per parity arm), then instantiates the
    // `induction` schema. This is `evenOrOdd` (add-form), fully accelerated-free.
    ctx.ok(&.{ "check", "tests/cases/cooper_parity.bpa" }, "OK: 15 declarations, 1 theorems proven\n");

    // The cooper link's DECLARED BOUNDARY: a multi-fixed-variable ∀∀∃
    // (`forall a, b; exists c; …`) is decided valid by Presburger but declines
    // — cooperInduction synthesizes an induction on a SINGLE variable. Without
    // a fallback, default mode is a hard error listing every link's decline
    // (the "solvable by arithmetic, not yet certifiable" gap)...
    ctx.fail(&.{ "check", "tests/cases/cooper_gap_raw.bpa" },
        \\tests/cases/cooper_gap_raw.bpa:25:9: error: 'arithmetic' is valid but no certifier could prove it here:
        \\  - equation/order/exists: form not in certification scope
        \\  - mixed-skeleton: form not in certification scope
        \\  - farkas: theory lacks symbol 'less_than'
        \\  - cooper: form not in certification scope
        \\use --fast to accept the accelerated verdict
        \\
    );
    // ...and --fast accepts the accelerated verdict, marking the theorem accelerated.
    ctx.ok(&.{ "check", "--fast", "tests/cases/cooper_gap_raw.bpa" },
        \\OK: 15 declarations, 1 theorems proven (0 elaborated, 1 accelerated: arithmetic)
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );
    // ...and `[by arithmetic fallback(<thm>)]` closes the gap fully elaborated in default
    // mode: the chain declines, so the cited manual theorem (which reduces the
    // ∀∀∃ to the cooper-certified single-variable evenOrOddArith) stands as the
    // certificate — no --fast, no acceleration.
    ctx.ok(&.{ "check", "tests/cases/cooper_gap.bpa" }, "OK: 17 declarations, 3 theorems proven\n");

    // Milestone D2: mixed skeletons replay as elaborated certificates
    ctx.ok(&.{ "check", "tests/cases/smt_cert.bpa" }, "OK: 143 declarations, 40 theorems proven\n");

    // mixed countermodel: arithmetic values plus opaque truth values
    ctx.fail(&.{ "check", "tests/cases/smt_bad.bpa" }, "tests/cases/smt_bad.bpa:12:9: error: arithmetic: false at a := 0, p := false\n");

    // instantiating strongInduction re-checks its full stored proof
    ctx.ok(&.{ "check", "tests/cases/strong_induction.bpa" }, "OK: 125 declarations, 40 theorems proven\n");
}
