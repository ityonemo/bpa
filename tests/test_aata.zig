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
    // (composition associativity/preservation + invertible⟺bijective, BOTH
    // directions). The backward direction (bijective ⇒ invertible) constructs the
    // inverse by definite description (the `functionFromGraph` axiom-schema — the
    // total+unique preimage graph realized as a function). Verified; the one
    // theorem resting on that disclosed axiom.
    ctx.ok(&.{ "check", "aata/1.2.2-functions.md" }, "OK: 49 declarations, 12 theorems proven\n");

    // AATA relations: the FOL-tractable part of Chapter 1 §1.2.3 — the three
    // equivalence-projections + the "reflexivity is redundant" exercise. The
    // equivalence⇔partition correspondence is deferred (needs sets-of-sets).
    ctx.ok(&.{ "check", "aata/1.2.3-relations.md" }, "OK: 27 declarations, 4 theorems proven\n");

    // AATA equivalence classes/partitions (§1.2.3): classes are nonempty, [x]=[y]
    // iff x~y, any two are equal-or-disjoint, AND the classes FORM A PARTITION —
    // covers the universe (⋃[x] = universe) and are pairwise-disjoint, discharging
    // isPartition. The partition packaging (a set of sets) is now stateable via
    // std/collection.bpa (a Collection = a set of Sets, modeling std/set.bpa one
    // level up). Fully proven, no holes.
    ctx.ok(&.{ "check", "aata/1.2.3-partitions.md" }, "OK: 145 declarations, 28 theorems proven\n");

    // AATA Chapter 2 "The Integers", §2.1 Mathematical Induction, fully proven —
    // the base case AND the ∀n≥0 3|(4ⁿ−1) nonneg-induction (its inductive step
    // splits 4^(k+1)−1 = 4(4ᵏ−1)+3 and uses dividesMul/dividesAdd), plus the
    // Second Principle (strong induction) and the Principle of Well-Ordering,
    // both aliased from std/integer-wellordering.bpa (proved there from ordinary
    // induction). No hole; the file checks WITHOUT --draft.
    ctx.ok(&.{ "check", "aata/2.1-induction.md" }, "OK: 271 declarations, 56 theorems proven\n");
    // §2.2 The Division Algorithm: Ch1-style — the proofs now live in
    // std/integer-division.bpa; this file aliases them and narrates. Existence
    // over all of ℤ + uniqueness.
    ctx.ok(&.{ "check", "aata/2.2-division-algorithm.md" }, "OK: 328 declarations, 73 theorems proven\n");
    // §2.3 Primes: stub for the GCD/Bézout/Euclid/FTA material to come; imports
    // the division library and aliases the two headline theorems.
    ctx.ok(&.{ "check", "aata/2.3-primes.md" }, "OK: 478 declarations, 98 theorems proven\n");
}
