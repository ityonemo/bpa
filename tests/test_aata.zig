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
    ctx.okSilent(&.{ "check", "aata/3.2-groups.md" });

    // AATA §3.3 Subgroups: the literate transliteration of the subgroup definition,
    // the one-step subgroup test (both directions), and the intersection-of-
    // subgroups exercise. Aliases std/subgroup.bpa to the book's H ≤ G notation;
    // concrete example subgroups (ℚ*, SL₂, ℤ₄, ℤ₂×ℤ₂) are summarized, not formalized
    // (Tier-3 carriers). Proven; no accelerated tactic.
    ctx.okSilent(&.{ "check", "aata/3.3-subgroups.md" });

    // AATA set theory: the literate transliteration of Chapter 1 §1.2.1
    // (the set-algebra proposition + De Morgan's laws proved by hand; the §1.2
    // exercises discharged in one line each by the `ext` tactic).
    ctx.okSilent(&.{ "check", "aata/1.2.1-sets.md" });

    // AATA functions: the literate transliteration of Chapter 1 §1.2.2
    // (composition associativity/preservation + invertible⟺bijective, BOTH
    // directions). The backward direction (bijective ⇒ invertible) constructs the
    // inverse by definite description (the `functionFromGraph` axiom-schema — the
    // total+unique preimage graph realized as a function). Verified; the one
    // theorem resting on that disclosed axiom.
    ctx.okSilent(&.{ "check", "aata/1.2.2-functions.md" });

    // AATA relations: the FOL-tractable part of Chapter 1 §1.2.3 — the three
    // equivalence-projections + the "reflexivity is redundant" exercise. The
    // equivalence⇔partition correspondence is deferred (needs sets-of-sets).
    ctx.okSilent(&.{ "check", "aata/1.2.3-relations.md" });

    // AATA equivalence classes/partitions (§1.2.3): classes are nonempty, [x]=[y]
    // iff x~y, any two are equal-or-disjoint, AND the classes FORM A PARTITION —
    // covers the universe (⋃[x] = universe) and are pairwise-disjoint, discharging
    // isPartition. The partition packaging (a set of sets) is now stateable via
    // std/collection.bpa (a Collection = a set of Sets, modeling std/set.bpa one
    // level up). Fully proven, no holes.
    ctx.okSilent(&.{ "check", "aata/1.2.3-partitions.md" });

    // AATA Chapter 2 "The Integers", §2.1 Mathematical Induction, fully proven —
    // the base case AND the ∀n≥0 3|(4ⁿ−1) nonneg-induction (its inductive step
    // splits 4^(k+1)−1 = 4(4ᵏ−1)+3 and uses dividesMul/dividesAdd), plus the
    // Second Principle (strong induction) and the Principle of Well-Ordering,
    // both aliased from std/integer-wellordering.bpa (proved there from ordinary
    // induction). No hole; the file checks WITHOUT --draft.
    ctx.okSilent(&.{ "check", "aata/2.1-induction.md" });
    // §2.2 The Division Algorithm: Ch1-style — the proofs now live in
    // std/integer-division.bpa; this file aliases them and narrates. Existence
    // over all of ℤ + uniqueness.
    ctx.okSilent(&.{ "check", "aata/2.2-division-algorithm.md" });
    // §2.3 Primes: stub for the GCD/Bézout/Euclid/FTA material to come; imports
    // the division library and aliases the two headline theorems.
    ctx.okSilent(&.{ "check", "aata/2.3-primes.md" });
}
