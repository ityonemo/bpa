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

    // the order theory + strong induction + well-ordering, split into its own
    // layer; proven, and --recursive re-verifies the imported peano proofs too
    ctx.ok(&.{ "check", "std/peano-ordering.bpa" }, "OK: 118 declarations, 38 theorems proven\n");

    ctx.ok(&.{ "check", "std/peano-ordering.bpa" }, "OK: 118 declarations, 38 theorems proven\n");

    // truncated subtraction + the gcd measure lemma (Euclid foundation)
    ctx.ok(&.{ "check", "std/peano-subtraction.bpa" }, "OK: 153 declarations, 44 theorems proven\n");

    // divisibility + guarded Euclidean div/mod + the gcd bridge lemma
    ctx.ok(&.{ "check", "std/peano-division.bpa" }, "OK: 205 declarations, 54 theorems proven\n");

    // THE PAYOFF: Euclid's algorithm, proved correct (common divisor +
    // greatest), by strong induction on the decreasing modulus
    ctx.ok(&.{ "check", "std/peano-gcd.bpa" }, "OK: 228 declarations, 56 theorems proven\n");

    // parity: even/odd + the crux 2|p² → 2|p, proven (no accelerated tactic)
    ctx.ok(&.{ "check", "std/peano-parity.bpa" }, "OK: 245 declarations, 59 theorems proven\n");

    // the integers ℤ ring algebra (std/integer-ring.bpa): left/right recursion,
    // commutativity, associativity, the additive-inverse law n+(-n)=0, and the
    // mul lemmas — all proven from the ℤ axioms by bidirectional induction.
    ctx.ok(&.{ "check", "std/integer-ring.bpa" }, "OK: 60 declarations, 17 theorems proven\n");

    // ℤ subtraction (total: a-b = a+(-b)) + the strict/non-strict order, over
    // the ring algebra. The order's gap witness is pinned NONNEGATIVE (an
    // unconstrained ℤ gap would make less_than the total relation — the naive
    // Peano port was a latent bug); irreflexivity rests on nonnegSuccNotZero (ℤ's
    // distinctness axiom, on the nonneg subclass). Full order corpus proven:
    // irreflexivity/transitivity/trichotomy (bidirectional induction on the
    // difference), addition preserves/cancels order, less_or_equal refl/trans/
    // split/antisymmetric. subSelf/subAddCancel from the inverse law, no induction.
    ctx.ok(&.{ "check", "std/integer-order.bpa" }, "OK: 142 declarations, 43 theorems proven\n");

    // strong induction + the Principle of Well-Ordering over the NONNEGATIVE
    // integers (std/integer-wellordering.bpa), layered above the ℤ order (it can't
    // live in integer-nonneg, which sits below the order in the import DAG).
    // nonnegStrongInduction (course-of-values) and nonnegWellOrdering (every
    // nonempty nonneg subset has a least element) — nonneg-guarded ports of the
    // peano-ordering proofs; the Division Algorithm's existence half runs on these.
    ctx.ok(&.{ "check", "std/integer-wellordering.bpa" }, "OK: 173 declarations, 47 theorems proven\n");

    // abstract divisibility (std/divisibility.bpa): a carrier with mul/add/ONE
    // and the divides predicate; dividesRefl/dividesMul/dividesAdd proved once,
    // over the abstract carrier. ℕ and ℤ `model` this to inherit them.
    ctx.ok(&.{ "check", "std/divisibility.bpa" }, "OK: 13 declarations, 3 theorems proven\n");

    // ℤ divisibility + powers (std/integer-divides.bpa): `divides` intro/elim +
    // pow recursion; the three basic facts (refl/mul/add) TRANSFER from the
    // abstract divisibility theory via `model IntegerDivisibility`.
    ctx.ok(&.{ "check", "std/integer-divides.bpa" }, "OK: 104 declarations, 23 theorems proven\n");

    // the ℤ Division Algorithm (std/integer-division.bpa): existence over all of
    // ℤ (via well-ordering on {a−bk≥0}) + uniqueness, with the supporting
    // product-of-nonnegatives / bounded-multiple-is-zero / remainder-difference
    // machinery. The reusable foundation for GCD / Bézout / the FTA.
    ctx.ok(&.{ "check", "std/integer-division.bpa" }, "OK: 310 declarations, 73 theorems proven\n");

    // the group theory (std/group.bpa): THREE axioms (associativity + LEFT identity
    // + LEFT inverse) + an opt-in `opCommutative`; the right-sided laws and the
    // basic-property theorems (identityUnique, inverseUnique, invProduct, cancelLeft,
    // …) are proved from those axioms alone. aata/3.2-groups.md aliases these.
    ctx.ok(&.{ "check", "std/group.bpa" }, "OK: 20 declarations, 12 theorems proven\n");

    // group powers (std/group-power.bpa): g^n over a Nat exponent, layered over
    // std/group.bpa + std/peano.bpa (keeping the core group theory import-free).
    // Defines pow(g,n) recursively and proves the exponent-addition law
    // powAdd: pow(g, m+n) = op(pow(g,m), pow(g,n)) by induction on n.
    ctx.ok(&.{ "check", "std/group-power.bpa" }, "OK: 87 declarations, 30 theorems proven\n");

    // subgroups (std/subgroup.bpa, Judson §3.3): a STANDALONE theory (declares its own
    // parent group) — the subgroup criteria, the one-step test (both directions), the
    // intersection, and the five group axioms proven on the subgroup (what a group-
    // model @-projects). Authored to plug into std/group.bpa via a model stack.
    ctx.ok(&.{ "check", "std/subgroup.bpa" }, "OK: 38 declarations, 17 theorems proven\n");

    // the ring theory (std/ring.bpa): an additive abelian group + associative,
    // distributing multiplication. Its additive half MODELS std/group.bpa (a
    // TWO-LEVEL structure — a model inside a modelable theory). Judson's first
    // ring proposition (a·0=0·a=0; a(-b)=(-a)b=-(ab); (-a)(-b)=ab) is proved by
    // TRANSFERRING the additive-group cancelRight/inverseUnique/invInvolution
    // through the AdditiveGroup model rather than re-deriving them. Left-axiomatic:
    // only addZeroLeft/addNegLeft are axioms; the RIGHT laws (addZeroRight,
    // addNegRight) are the two derived theorems the model no longer needs to map.
    // (the synthetic materialized theorems are suppressed.)
    ctx.ok(&.{ "check", "std/ring.bpa" }, "OK: 42 declarations, 19 theorems proven\n");

    // ℤ as a thin model of the ring theory (std/integer-ring-model.bpa): the
    // THREE-LEVEL chain ℤ → ring → group. `model IntegerRing = Int` discharges
    // ring's 7 axioms from ℤ's facts (ring's RIGHT identity/inverse laws are now
    // derived theorems, so they are not mapped; associativity axioms now bind the canonical
    // a,b,c order, so ℤ's assoc theorems α-match the remapped ring axioms directly
    // — no binder-order adapters needed), and negMulNeg ((-a)(-b)=ab, new to ℤ)
    // transfers — its ring proof having itself transferred group.invInvolution
    // through ring's AdditiveGroup model, re-materialized here.
    ctx.ok(&.{ "check", "std/integer-ring-model.bpa" }, "OK: 120 declarations, 37 theorems proven\n");

    // the set theory (std/set.bpa): the membership axioms + extensionality, and
    // the 19 set-algebra identities (idempotence, identity, associativity,
    // commutativity, distributivity, De Morgan, difference laws) proved from them
    // by the extensionality→unfold→tautology recipe. Available for a structure to
    // `model` and inherit. The AATA transcription (aata/1.2.1-sets.md) aliases these.
    ctx.ok(&.{ "check", "std/set.bpa" }, "OK: 35 declarations, 19 theorems proven\n");

    // collections (std/collection.bpa): sets of sets, one level up. A Collection MODELS
    // std/set.bpa with set.Element -> Set, set.Set -> Collection, so the whole set
    // algebra transfers onto collections for free (contains = member one level up).
    // Plus the CROSS-LEVEL operations set.bpa lacks — bigUnion/bigIntersection
    // (collapse a collection to a set), a universe, and the partition apparatus
    // (covers / pairwiseDisjoint / isPartition) a quotient needs.
    ctx.ok(&.{ "check", "std/collection.bpa" }, "OK: 68 declarations, 22 theorems proven\n");

    // the function theory (std/function.bpa): axioms only, no theorems — a
    // direct check materializes nothing and exits nonzero with a warning.
    ctx.okCode(&.{ "check", "std/function.bpa" },
        \\OK: 18 declarations, 0 theorems proven
        \\  — WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).
        \\
    , 1);

    // invertible functions form a GROUP (std/function-invertible.bpa): the bijections
    // of a set under composition. A GUARDED model of std/group.bpa (guard = invertible)
    // — the group axioms proved on invertible functions (assoc/identities from funcExt;
    // inverse laws + closure under compose/inverse), then the group corpus (identity/
    // inverse uniqueness, involution, cancellation) transfers onto them for free.
    // Exercises cross-sort guarded weakening (group.Grp -> Fn where invertible).
    ctx.ok(&.{ "check", "std/function-invertible.bpa" }, "OK: 66 declarations, 23 theorems proven\n");
}
