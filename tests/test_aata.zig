//! Integration gates — the AATA literate transliterations (aata/*.md).
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

    // AATA group theory: the literate translation of Groups basic-
    // properties (5 propositions) + 5 in-scope exercises, verified (proven; no accelerated tactic).
    ctx.ok(&.{ "check", "aata/3.2-groups.md" }, "OK: 29 declarations, 10 theorems proven\n");

    // AATA set theory: the literate transliteration of Chapter 1 §1.2.1
    // (the set-algebra proposition + De Morgan's laws proved by hand; the §1.2
    // exercises discharged in one line each by the `ext` tactic).
    ctx.ok(&.{ "check", "aata/1.2.1-sets.md" }, "OK: 48 declarations, 19 theorems proven\n");

    // AATA functions: the literate transliteration of Chapter 1 §1.2.2
    // (composition associativity/preservation + invertible⇒bijective
    // forward), verified (proven; no accelerated tactic). The backward direction is a marked wall.
    ctx.ok(&.{ "check", "aata/1.2.2-functions.md" }, "OK: 46 declarations, 11 theorems proven\n");
}
