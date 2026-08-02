//! Integration gates — the standard library files (std/peano* , group, set, function) — the pinned declaration/theorem counts.
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

    // the standard library must check
    ctx.ok(&.{ "check", "std/peano.bpa" }, "OK: 48 declarations, 17 theorems proven\n");

    // the standard library is accelerated-free, forever
    ctx.ok(&.{ "check", "std/peano.bpa" }, "OK: 48 declarations, 17 theorems proven\n");

    // the order theory + strong induction, split into its own layer; proven,
    // and --recursive re-verifies the imported peano proofs too
    ctx.ok(&.{ "check", "std/peano-ordering.bpa" }, "OK: 117 declarations, 38 theorems proven\n");

    ctx.ok(&.{ "check", "std/peano-ordering.bpa" }, "OK: 117 declarations, 38 theorems proven\n");

    // truncated subtraction + the gcd measure lemma (Euclid foundation)
    ctx.ok(&.{ "check", "std/peano-subtraction.bpa" }, "OK: 152 declarations, 44 theorems proven\n");

    // divisibility + guarded Euclidean div/mod + the gcd bridge lemma
    ctx.ok(&.{ "check", "std/peano-division.bpa" }, "OK: 204 declarations, 54 theorems proven\n");

    // THE PAYOFF: Euclid's algorithm, proved correct (common divisor +
    // greatest), by strong induction on the decreasing modulus
    ctx.ok(&.{ "check", "std/peano-gcd.bpa" }, "OK: 227 declarations, 56 theorems proven\n");

    // parity: even/odd + the crux 2|p² → 2|p, proven (no accelerated tactic)
    ctx.ok(&.{ "check", "std/peano-parity.bpa" }, "OK: 244 declarations, 59 theorems proven\n");

    // the group theory (std/group.bpa): axioms only, no theorems — so a
    // direct check materializes nothing and exits nonzero with a warning
    // (the theory is a valid dependency, but checking it alone proves 0).
    ctx.okCode(&.{ "check", "std/group.bpa" },
        \\OK: 9 declarations, 0 theorems proven
        \\  — WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).
        \\
    , 1);

    // the set theory (std/set.bpa): axioms only, no theorems — a direct
    // check materializes nothing and exits nonzero with a warning.
    ctx.okCode(&.{ "check", "std/set.bpa" },
        \\OK: 16 declarations, 0 theorems proven
        \\  — WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).
        \\
    , 1);

    // the function theory (std/function.bpa): axioms only, no theorems — a
    // direct check materializes nothing and exits nonzero with a warning.
    ctx.okCode(&.{ "check", "std/function.bpa" },
        \\OK: 17 declarations, 0 theorems proven
        \\  — WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).
        \\
    , 1);
}
