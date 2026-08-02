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
    // properties (5 propositions) + 5 in-scope exercises, verified ELABORATED.
    ctx.ok(&.{ "check", "aata/3.2-groups.md" }, "OK: 29 declarations, 10 theorems proven\n");

    // AATA set theory: the literate transliteration of Chapter 1 §1.2.1
    // (the set-algebra proposition + De Morgan's laws), verified ELABORATED.
    ctx.ok(&.{ "check", "aata/1.2.1-sets.md" }, "OK: 43 declarations, 14 theorems proven\n");

    // AATA functions: the literate transliteration of Chapter 1 §1.2.2
    // (composition associativity/preservation + invertible⇒bijective
    // forward), verified ELABORATED. The backward direction is a marked wall.
    ctx.ok(&.{ "check", "aata/1.2.2-functions.md" }, "OK: 36 declarations, 7 theorems proven\n");
}
