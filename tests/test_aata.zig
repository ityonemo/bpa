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

    // AATA group theory: the literate translation of Groups basic-properties (5
    // propositions) + 5 in-scope exercises. The 10 theorems now ALIAS the library
    // proofs in std/group.bpa (the .md is book-notation presentation; the checked
    // derivations live in std) — verified (proven; no accelerated tactic).
    ctx.ok(&.{ "check", "aata/3.2-groups.md" }, "OK: 40 declarations, 12 theorems proven\n");

    // AATA §3.3 Subgroups: the literate transliteration of the subgroup definition,
    // the one-step subgroup test (both directions), and the intersection-of-
    // subgroups exercise. Aliases std/subgroup.bpa to the book's H ≤ G notation;
    // concrete example subgroups (ℚ*, SL₂, ℤ₄, ℤ₂×ℤ₂) are summarized, not formalized
    // (Tier-3 carriers). Proven; no accelerated tactic.
    ctx.ok(&.{ "check", "aata/3.3-subgroups.md" }, "OK: 54 declarations, 24 theorems proven\n");

    // AATA set theory: the literate transliteration of Chapter 1 §1.2.1
    // (the set-algebra proposition + De Morgan's laws proved by hand; the §1.2
    // exercises discharged in one line each by the `ext` tactic).
    ctx.ok(&.{ "check", "aata/1.2.1-sets.md" }, "OK: 69 declarations, 19 theorems proven\n");

    // AATA functions: the literate transliteration of Chapter 1 §1.2.2
    // (composition associativity/preservation + invertible⇒bijective
    // forward), verified (proven; no accelerated tactic). The backward direction is a marked wall.
    ctx.ok(&.{ "check", "aata/1.2.2-functions.md" }, "OK: 46 declarations, 11 theorems proven\n");

    // AATA relations: the FOL-tractable part of Chapter 1 §1.2.3 — the three
    // equivalence-projections + the "reflexivity is redundant" exercise. The
    // equivalence⇔partition correspondence is deferred (needs sets-of-sets).
    ctx.ok(&.{ "check", "aata/1.2.3-relations.md" }, "OK: 27 declarations, 4 theorems proven\n");

    // AATA equivalence classes/partitions: the tractable heart of §1.2.3 —
    // classes are nonempty, [x]=[y] iff x~y, and any two are equal-or-disjoint
    // (3 theorems). The "form a partition" packaging (a set of sets) stays a
    // `hole`, so the file needs --draft; default mode rejects it, naming the
    // one remaining hole.
    ctx.ok(&.{ "check", "--draft", "aata/1.2.3-partitions.md" },
        \\OK: 95 declarations, 22 theorems proven
        \\  — DRAFT — 1 hole(s) unfilled (aspirational; the result is conditional on them): classesCoverUniverse; re-run `bpa check` (no --draft) once filled.
        \\
    );
    ctx.fail(&.{ "check", "aata/1.2.3-partitions.md" },
        \\error: 1 hole(s) remain (default mode rejects holes; use --draft while filling them):
        \\  - classesCoverUniverse  (aata/1.2.3-partitions.md:596)
        \\
    );

    // AATA Chapter 2 "The Integers": §2.1 Mathematical Induction, fully proven —
    // the base case AND the ∀n≥0 3|(4ⁿ−1) nonneg-induction (its inductive step
    // splits 4^(k+1)−1 = 4(4ᵏ−1)+3 and uses dividesMul/dividesAdd). No hole; the
    // file checks WITHOUT --draft.
    ctx.ok(&.{ "check", "aata/2-integers.md" }, "OK: 184 declarations, 27 theorems proven\n");
}
