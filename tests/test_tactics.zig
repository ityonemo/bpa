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

    // simplify always emits kernel steps (never accelerates): the default check accepts it
    ctx.ok(&.{ "check", "tests/cases/simplify.bpa" }, "OK: 13 declarations, 2 theorems proven\n");

    // unjoinable normal forms: the diagnostic shows both, copy-pasteable
    ctx.fail(&.{ "check", "tests/cases/simplify_bad.bpa" }, "tests/cases/simplify_bad.bpa:14:13: error: simplify: normal forms differ: 'add(n, ZERO)' vs 'n'\n");

    // cycling rules hit the hard rewrite cap instead of hanging
    ctx.fail(&.{ "check", "tests/cases/simplify_loop.bpa" }, "tests/cases/simplify_loop.bpa:13:9: error: simplify: rewrite limit reached (looping rule set?)\n");

    // ac: associative-commutative sum reordering over opaque atoms, emits kernel steps
    ctx.ok(&.{ "check", "tests/cases/ac.bpa" }, "OK: 59 declarations, 19 theorems proven\n");

    // ac over multiplication: same bubble-sort machinery, mul lemma triple
    // (mulIsAssociative/mulIsCommutative/mulLeftSwap), emits kernel steps
    ctx.ok(&.{ "check", "tests/cases/ac_mul.bpa" }, "OK: 59 declarations, 18 theorems proven\n");

    // ac_quantified: peel the forall prefix then run the ac core (add + mul)
    ctx.ok(&.{ "check", "tests/cases/ac_quantified.bpa" }, "OK: 60 declarations, 19 theorems proven\n");

    // distributivity: ac_quantified with a cited distributivity lemma
    // pre-normalizes (distributes) each side before the AC bubble-sort
    ctx.ok(&.{ "check", "tests/cases/distribute.bpa" }, "OK: 57 declarations, 18 theorems proven\n");

    // `polynomial(theory)`: nonlinear identities canonicalize, emitting kernel
    // steps (no accelerated tactic) via distribute → sort monomials → sort sum → fold.
    ctx.ok(&.{ "check", "tests/cases/polynomial.bpa" }, "OK: 54 declarations, 19 theorems proven\n");

    // sides with different expansions → located error, exit 1 (not accelerated)
    ctx.fail(&.{ "check", "tests/cases/polynomial_bad.bpa" }, "tests/cases/polynomial_bad.bpa:18:9: error: polynomial: sides expand differently: 'add(mul(b, b), add(mul(b, a), add(mul(b, a), mul(a, a))))' vs 'add(mul(b, b), mul(a, a))'\n");

    // `ext(theory)`: the extensionality tactic, one tactic over two models —
    // reduce an equation to its pointwise obligation via the theory's
    // extensionality lemma, unfold the operators, close the residue. SET model
    // (propositional residue → tautology); emits kernel steps.
    ctx.ok(&.{ "check", "tests/cases/ext_set.bpa" }, "OK: 47 declarations, 21 theorems proven\n");
    // FUNCTION model (equational residue → rewrite join) — same `ext` tactic.
    ctx.ok(&.{ "check", "tests/cases/ext_function.bpa" }, "OK: 29 declarations, 3 theorems proven\n");
    // a FALSE set identity: the pointwise residue has a countermodel, so ext
    // declines with a located error (exit 1) — never accepts a false equation.
    ctx.fail(&.{ "check", "tests/cases/ext_bad.bpa" }, "tests/cases/ext_bad.bpa:18:9: error: ext: could not close the pointwise obligation propositionally (is the identity true?)\n");

    // `model`: structure reuse. The source theory (a carrier + op + left-unit +
    // one proven theorem) is modeled by a concrete sort, and its theorem
    // transfers, remapped through the model. See MODEL-DESIGN.md.
    ctx.ok(&.{ "check", "tests/cases/model_source.bpa" }, "OK: 6 declarations, 2 theorems proven\n");

    // --fast trusts the transfer wholesale (remap the source theorem, α-match the
    // goal, taint accelerated: model) — checks nothing about the source proof.
    ctx.ok(&.{ "check", "--fast", "tests/cases/model_transfer.bpa" },
        \\OK: 13 declarations, 3 theorems proven (1 accelerated: model)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );
    // default (strict) MATERIALIZES the remapped source proof as a synthetic
    // kernel-checked theorem (suppressed from the count) and cites it — so it
    // passes with NO taint. The transfer is genuinely kernel-verified.
    ctx.ok(&.{ "check", "tests/cases/model_transfer.bpa" }, "OK: 13 declarations, 3 theorems proven\n");

    // DEPENDENCY WALK: transferring a source theorem whose proof cites ANOTHER
    // source theorem forces strict materialization to recurse into it (memoized —
    // the shared dependency materializes once across both cites). Kernel-checked.
    ctx.ok(&.{ "check", "tests/cases/model_recurse.bpa" }, "OK: 14 declarations, 4 theorems proven\n");
    ctx.ok(&.{ "check", "--fast", "tests/cases/model_recurse.bpa" },
        \\OK: 14 declarations, 4 theorems proven (2 accelerated: model)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // MATERIALIZATION CITATION RULE: a materialized model proof may cite another
    // materialized theorem; a substitution-INVARIANT theorem/axiom (as-is, walk
    // ends); or a substituted axiom mapped (to a theorem OR an axiom). It may NOT
    // cite a fact the substitution AFFECTS but the model doesn't map.
    // OK exercises invariant-theorem + invariant-axiom + axiom→theorem + axiom→axiom:
    ctx.ok(&.{ "check", "tests/cases/model_cite_ok.bpa" }, "OK: 20 declarations, 4 theorems proven\n");
    // BAD leaves an affected axiom (opUnitRight, cited by the transferred proof)
    // unmapped → rejected, naming it.
    ctx.fail(&.{ "check", "tests/cases/model_cite_bad.bpa" }, "tests/cases/model_cite_bad.bpa:33:27: error: model materialization cites axiom 'opUnitRight', which the substitution affects but the model does not map; add a mapping for it\n");

    // GUARDED model (`model … where <pred>`): the transfer is RELATIVIZED — every
    // carrier ∀ gains `guard(x) ->` — and strict materialization discharges the
    // guard obligation at each forall_elim over a guarded universal (recursing on
    // the instantiation term: constant → base closure fact; eigenvariable → the
    // in-scope `assume guard(a)`; composite → a closure fact + recursion). Fully
    // kernel-checked, no taint.
    ctx.ok(&.{ "check", "tests/cases/model_guarded_source.bpa" }, "OK: 7 declarations, 3 theorems proven\n");
    ctx.ok(&.{ "check", "tests/cases/model_guarded.bpa" }, "OK: 19 declarations, 6 theorems proven\n");

    // SOUNDNESS: even under --fast, the remapped source theorem must α-match the
    // goal — a flipped-equation goal is rejected (you can't prove what the source
    // theorem doesn't say).
    ctx.fail(&.{ "check", "--fast", "tests/cases/model_bad.bpa" },
        \\tests/cases/model_bad.bpa:24:9: error: model transfer of 'source.opUnitLeftTwice' does not match the goal:
        \\  transferred: forall a: Thing; combine(ZED, combine(ZED, a)) = combine(ZED, a)
        \\  goal:        forall a: Thing; combine(ZED, a) = combine(ZED, combine(ZED, a))
        \\
    );

    // the polynomial ACCELERATED TACTIC: a thin theory (no ring lemmas) DECLINES under
    // the default (needs a lemma), but --fast decides it structurally and
    // is accelerated (accelerated: polynomial).
    ctx.fail(&.{ "check", "tests/cases/polynomial_oracle.bpa" }, "tests/cases/polynomial_oracle.bpa:22:9: error: polynomial: needs mulAddDistribLeft in scope\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oracle.bpa" },
        \\OK: 6 declarations, 1 theorems proven (1 accelerated: polynomial)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // Regression: the lemma-free accelerated tactic normalizer distributes a wide-sum 4th
    // power (256 monomials); building each product reallocates the term pool,
    // which pool.args aliases — the old code read a dangling arg slice and
    // panicked. Must check clean under --fast (never crash).
    ctx.ok(&.{ "check", "--fast", "tests/cases/polynomial_oob.bpa" },
        \\OK: 6 declarations, 1 theorems proven (1 accelerated: polynomial)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // ac on different multisets reports the mismatch (emits kernel steps, not accelerated)
    ctx.fail(&.{ "check", "tests/cases/ac_bad.bpa" }, "tests/cases/ac_bad.bpa:18:17: error: assoc_commut: sides have different summands: 'add(b, add(a, a))' vs 'add(b, a)'\n");

    // assoc_commut(assoc, comm, swap): the explicit-triple form on a CUSTOM
    // operator (emits kernel steps — the triple is kernel-checked).
    ctx.ok(&.{ "check", "tests/cases/assoc_commut_custom.bpa" }, "OK: 7 declarations, 2 theorems proven\n");

    // no partials: 1 or 2 args is an error (either bare or exactly three).
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_bad_arity.bpa" }, "tests/cases/assoc_commut_bad_arity.bpa:12:9: error: assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got 2\n");

    // the assoc_commut ACCELERATED TACTIC: bare form on a thin theory (no AC lemmas)
    // DECLINES by default, but --fast decides structurally and is accelerated.
    ctx.fail(&.{ "check", "tests/cases/assoc_commut_oracle.bpa" }, "tests/cases/assoc_commut_oracle.bpa:16:9: error: assoc_commut: needs addIsAssociative in scope\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/assoc_commut_oracle.bpa" },
        \\OK: 4 declarations, 1 theorems proven (1 accelerated: assoc_commut)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // `assoc(assocLemma)`: associativity-only reorder on a CUSTOM operator
    // (no add/mul assumption). Emits kernel steps.
    ctx.ok(&.{ "check", "tests/cases/assoc.bpa" }, "OK: 6 declarations, 3 theorems proven\n");

    // sides differ by more than associativity (operands permuted) → error
    ctx.fail(&.{ "check", "tests/cases/assoc_bad.bpa" }, "tests/cases/assoc_bad.bpa:11:9: error: assoc: sides differ by more than associativity: 'op(a, b)' vs 'op(b, a)'\n");

    // the required-arg contract: bare `assoc` is an error
    ctx.fail(&.{ "check", "tests/cases/assoc_missing_arg.bpa" }, "tests/cases/assoc_missing_arg.bpa:10:9: error: assoc requires an associativity lemma: assoc(<assocLemma>); got 0 argument(s)\n");

    // the assoc ACCELERATED TACTIC: certifies by default, --fast is accelerated
    ctx.ok(&.{ "check", "tests/cases/assoc_oracle.bpa" }, "OK: 4 declarations, 1 theorems proven\n");

    ctx.ok(&.{ "check", "--fast", "tests/cases/assoc_oracle.bpa" },
        \\OK: 4 declarations, 1 theorems proven (1 accelerated: assoc)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // simplify_quantified: peel forall over an equation, emits kernel steps
    ctx.ok(&.{ "check", "tests/cases/simplify_quantified.bpa" }, "OK: 8 declarations, 2 theorems proven\n");

    // simplify_quantified on a bare equation redirects to simplify
    ctx.fail(&.{ "check", "tests/cases/simplify_quantified_bad.bpa" }, "tests/cases/simplify_quantified_bad.bpa:12:9: error: simplify_quantified expects a quantified goal; did you mean simplify?\n");

    // plain simplify on a quantified goal redirects to simplify_quantified
    ctx.fail(&.{ "check", "tests/cases/simplify_on_quantified.bpa" }, "tests/cases/simplify_on_quantified.bpa:12:9: error: simplify proves equations; did you mean simplify_quantified?\n");

    // symmetry: y = x from x = y in one step, emits kernel steps
    ctx.ok(&.{ "check", "tests/cases/symmetry.bpa" }, "OK: 6 declarations, 1 theorems proven\n");

    // Milestone B2: tautology emits certificates — kernel-checked steps,
    // emits kernel steps, not accelerated (the accelerated path remains as the over-budget fallback)
    ctx.ok(&.{ "check", "tests/cases/tautology.bpa" }, "OK: 9 declarations, 5 theorems proven\n");

    // certificates check with every step kernel-checked by default (no accelerated tactic)
    ctx.ok(&.{ "check", "tests/cases/tautology.bpa" }, "OK: 9 declarations, 5 theorems proven\n");

    // non-consequence: the diagnostic carries the countermodel
    ctx.fail(&.{ "check", "tests/cases/tautology_bad.bpa" }, "tests/cases/tautology_bad.bpa:10:9: error: tautology: not a propositional consequence; countermodel: p := true, q := false\n");

    // the atom cap is a hard, honest limit
    ctx.fail(&.{ "check", "tests/cases/tautology_cap.bpa" }, "tests/cases/tautology_cap.bpa:25:9: error: tautology: 17 distinct atoms exceeds the limit of 16\n");

    // Milestone C: arithmetic accelerated tactic — Presburger quantifier elimination
    ctx.ok(&.{ "check", "--fast", "tests/cases/arithmetic.bpa" },
        \\OK: 9 declarations, 4 theorems proven (4 accelerated: arithmetic)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // false statement: the diagnostic carries countermodel values
    ctx.fail(&.{ "check", "tests/cases/arithmetic_bad.bpa" }, "tests/cases/arithmetic_bad.bpa:17:17: error: arithmetic: false at a := 0, b := 0\n");

    // a relation opaque only because it hides a nonlinear term is
    // reported honestly as outside the fragment, not as a false countermodel
    ctx.fail(&.{ "check", "tests/cases/arithmetic_frag.bpa" }, "tests/cases/arithmetic_frag.bpa:15:9: error: arithmetic: 'mul(a, b)' is outside linear arithmetic\n");

    // Milestone D: the SMT combination — mixed goals, one accelerated-tactic name
    ctx.ok(&.{ "check", "--fast", "tests/cases/smt.bpa" },
        \\OK: 9 declarations, 2 theorems proven (2 accelerated: arithmetic)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );

    // Milestone C2b: universal linear goals replay as kernel-checked certificates
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

    // Milestone C2a: ground goals replay as kernel-checked simplify certificates
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
        \\OK: 15 declarations, 1 theorems proven (1 accelerated: arithmetic)
        \\  — NOT FULLY VERIFIED: accelerated (a procedure's verdict was trusted without a kernel derivation); re-run `bpa check` to fully verify.
        \\
    );
    // ...and `[by arithmetic fallback(<thm>)]` closes the gap fully proven in default
    // mode: the chain declines, so the cited manual theorem (which reduces the
    // ∀∀∃ to the cooper-certified single-variable evenOrOddArith) stands as the
    // certificate — no --fast, no acceleration.
    ctx.ok(&.{ "check", "tests/cases/cooper_gap.bpa" }, "OK: 17 declarations, 3 theorems proven\n");

    // Milestone D2: mixed skeletons replay as kernel-checked certificates
    ctx.ok(&.{ "check", "tests/cases/smt_cert.bpa" }, "OK: 143 declarations, 40 theorems proven\n");

    // mixed countermodel: arithmetic values plus opaque truth values
    ctx.fail(&.{ "check", "tests/cases/smt_bad.bpa" }, "tests/cases/smt_bad.bpa:12:9: error: arithmetic: false at a := 0, p := false\n");

    // instantiating strongInduction re-checks its full stored proof
    ctx.ok(&.{ "check", "tests/cases/strong_induction.bpa" }, "OK: 125 declarations, 40 theorems proven\n");
}
