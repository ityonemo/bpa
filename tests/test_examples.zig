//! Integration gates — the examples/ corpus (peano, gauss, euclid, sqrt2, literate).
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

    // the living demo: automation-assisted PA — simplify inside the
    // inductions and pure arithmetic certificates throughout. Since Cooper-
    // replay landed, even evenOrOdd (∀∃) certifies, so --fast defers nothing
    // and reports all six pure (the banner still fires: --fast mode is on).
    ctx.ok(&.{ "check", "--fast", "examples/peano.bpa" },
        \\OK: 18 declarations, 6 theorems proven
        \\  — NOT FULLY VERIFIED (deferred: arithmetic-certificates); re-run `bpa check` before finalizing.
        \\
    );

    // ...and under the DEFAULT (verify everything) it is now PURE too: the
    // evenOrOdd oracle step (∀∃, Cooper-QE) certifies via the cooper link's
    // synthesized induction (period-2 parity split), so all six theorems are
    // proven with no oracle taint.
    ctx.ok(&.{ "check", "examples/peano.bpa" }, "OK: 18 declarations, 6 theorems proven\n");

    // the by-hand twin: every induction case in primitive rules
    ctx.ok(&.{ "check", "examples/peano-pure.bpa" }, "OK: 13 declarations, 3 theorems proven\n");

    // the incorrect-proof showcase: three classic mistakes, three exact
    // diagnostics (this file is documentation; its output is the contract)
    ctx.fail(&.{ "check", "examples/incorrect.bpa" },
        \\examples/incorrect.bpa:39:41: error: modus_ponens: expected antecedent 'raining', got 'wet'
        \\examples/incorrect.bpa:61:4: error: step claims 'forall n: Nat; is_zero(n)' but forall_intro derives 'forall n: Nat; is_zero(ZERO)'
        \\examples/incorrect.bpa:73:28: error: unproved obligation: 'ZERO != ZERO'
        \\
    );

    // Gauss's summation formula, by hand, proved pure over the imported base
    ctx.ok(&.{ "check", "examples/gauss-pure.bpa" }, "OK: 70 declarations, 19 theorems proven\n");

    // the automation-assisted twin: `ac` replaces the by-hand exchange
    // lemma, still pure
    ctx.ok(&.{ "check", "examples/gauss.bpa" }, "OK: 70 declarations, 18 theorems proven\n");

    // Euclid's algorithm from a consumer's view: import the verified gcd
    // library and cite its correctness theorems to derive concrete facts
    ctx.ok(&.{ "check", "examples/euclid.bpa" }, "OK: 236 declarations, 59 theorems proven\n");

    ctx.ok(&.{ "check", "examples/euclid-compute.bpa" }, "OK: 259 declarations, 61 theorems proven\n");

    // √2 is irrational (stated over ℕ), proved PURE — the headline result.
    ctx.ok(&.{ "check", "examples/sqrt2.bpa" }, "OK: 291 declarations, 62 theorems proven\n");

    // literate: `check` on a .md checks its ```bpa blocks (prose masked).
    ctx.ok(&.{ "check", "examples/literate.md" }, "OK: 6 declarations, 1 theorems proven\n");
}
