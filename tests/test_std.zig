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
    ctx.okSilent(&.{ "check", "std/peano.bpa" });

    // the order theory + strong induction + well-ordering, split into its own
    // layer; proven, and --recursive re-verifies the imported peano proofs too
    ctx.okSilent(&.{ "check", "std/peano-ordering.bpa" });

    ctx.okSilent(&.{ "check", "std/peano-ordering.bpa" });

    // truncated subtraction + the gcd measure lemma (Euclid foundation)
    ctx.okSilent(&.{ "check", "std/peano-subtraction.bpa" });

    // divisibility + guarded Euclidean div/mod + the gcd bridge lemma
    ctx.okSilent(&.{ "check", "std/peano-division.bpa" });

    // THE PAYOFF: Euclid's algorithm, proved correct (common divisor +
    // greatest), by strong induction on the decreasing modulus
    ctx.okSilent(&.{ "check", "std/peano-gcd.bpa" });

    // parity: even/odd + the crux 2|p² → 2|p, proven (no accelerated tactic)
    ctx.okSilent(&.{ "check", "std/peano-parity.bpa" });

    // the integers ℤ ring algebra (std/integer-ring.bpa): left/right recursion,
    // commutativity, associativity, the additive-inverse law n+(-n)=0, and the
    // mul lemmas — all proven from the ℤ axioms by bidirectional induction.
    ctx.okSilent(&.{ "check", "std/integer-ring.bpa" });

    // ℤ subtraction (total: a-b = a+(-b)) + the strict/non-strict order, over
    // the ring algebra. The order's gap witness is pinned NONNEGATIVE (an
    // unconstrained ℤ gap would make less_than the total relation — the naive
    // Peano port was a latent bug); irreflexivity rests on nonnegSuccNotZero (ℤ's
    // distinctness axiom, on the nonneg subclass). Full order corpus proven:
    // irreflexivity/transitivity/trichotomy (bidirectional induction on the
    // difference), addition preserves/cancels order, less_or_equal refl/trans/
    // split/antisymmetric. subSelf/subAddCancel from the inverse law, no induction.
    ctx.okSilent(&.{ "check", "std/integer-order.bpa" });

    // strong induction + the Principle of Well-Ordering over the NONNEGATIVE
    // integers (std/integer-wellordering.bpa), layered above the ℤ order (it can't
    // live in integer-nonneg, which sits below the order in the import DAG).
    // nonnegStrongInduction (course-of-values) and nonnegWellOrdering (every
    // nonempty nonneg subset has a least element) — nonneg-guarded ports of the
    // peano-ordering proofs; the Division Algorithm's existence half runs on these.
    ctx.okSilent(&.{ "check", "std/integer-wellordering.bpa" });

    // abstract divisibility (std/divisibility.bpa): a carrier with mul/add/ONE
    // and the divides predicate; dividesRefl/dividesMul/dividesAdd proved once,
    // over the abstract carrier. ℕ and ℤ `model` this to inherit them.
    ctx.okSilent(&.{ "check", "std/divisibility.bpa" });

    // ℤ divisibility + powers (std/integer-divides.bpa): `divides` intro/elim +
    // pow recursion; the three basic facts (refl/mul/add) TRANSFER from the
    // abstract divisibility theory via `model IntegerDivisibility`.
    ctx.okSilent(&.{ "check", "std/integer-divides.bpa" });

    // the ℤ Division Algorithm (std/integer-division.bpa): existence over all of
    // ℤ (via well-ordering on {a−bk≥0}) + uniqueness, with the supporting
    // product-of-nonnegatives / bounded-multiple-is-zero / remainder-difference
    // machinery. The reusable foundation for GCD / Bézout / the FTA.
    ctx.okSilent(&.{ "check", "std/integer-division.bpa" });

    // finite integer sequences + products (std/integer-sequence.bpa): a `Seq` sort
    // with an `at(s,i)` accessor and a recursive `productUpTo(s,k)` (bpa has no
    // lists/finite products, and a func can't take a Nat->Int param, so the indexed
    // family is reified as a sort). everyEntryDividesProduct — each entry below the
    // bound divides the product — is the lemma the infinitude/FTA arguments need.
    // Plus the reification-existence axioms (seqSingletonExists/seqConcatExists/
    // seqRemoveExists) that let FTA witness/splice/cancel factorization sequences.
    ctx.okSilent(&.{ "check", "std/integer-sequence.bpa" });

    // the group theory (std/group.bpa): THREE axioms (associativity + LEFT identity
    // + LEFT inverse) + an opt-in `opCommutative`; the right-sided laws and the
    // basic-property theorems (identityUnique, inverseUnique, invProduct, cancelLeft,
    // …) are proved from those axioms alone. aata/3.2-groups.md aliases these.
    ctx.okSilent(&.{ "check", "std/group.bpa" });

    // group powers (std/group-power.bpa): g^n over a Nat exponent, layered over
    // std/group.bpa + std/peano.bpa (keeping the core group theory import-free).
    // Defines pow(g,n) recursively and proves the exponent-addition law
    // powAdd: pow(g, m+n) = op(pow(g,m), pow(g,n)) by induction on n.
    ctx.okSilent(&.{ "check", "std/group-power.bpa" });

    // subgroups (std/subgroup.bpa, Judson §3.3): a STANDALONE theory (declares its own
    // parent group) — the subgroup criteria, the one-step test (both directions), the
    // intersection, and the five group axioms proven on the subgroup (what a group-
    // model @-projects). Authored to plug into std/group.bpa via a model stack.
    ctx.okSilent(&.{ "check", "std/subgroup.bpa" });

    // the ring theory (std/ring.bpa): an additive abelian group + associative,
    // distributing multiplication. Its additive half MODELS std/group.bpa (a
    // TWO-LEVEL structure — a model inside a modelable theory). Judson's first
    // ring proposition (a·0=0·a=0; a(-b)=(-a)b=-(ab); (-a)(-b)=ab) is proved by
    // TRANSFERRING the additive-group cancelRight/inverseUnique/invInvolution
    // through the AdditiveGroup model rather than re-deriving them. Left-axiomatic:
    // only addZeroLeft/addNegLeft are axioms; the RIGHT laws (addZeroRight,
    // addNegRight) are the two derived theorems the model no longer needs to map.
    // (the synthetic materialized theorems are suppressed.)
    ctx.okSilent(&.{ "check", "std/ring.bpa" });

    // ℤ as a thin model of the ring theory (std/integer-ring-model.bpa): the
    // THREE-LEVEL chain ℤ → ring → group. `model IntegerRing = Int` discharges
    // ring's 7 axioms from ℤ's facts (ring's RIGHT identity/inverse laws are now
    // derived theorems, so they are not mapped; associativity axioms now bind the canonical
    // a,b,c order, so ℤ's assoc theorems α-match the remapped ring axioms directly
    // — no binder-order adapters needed), and negMulNeg ((-a)(-b)=ab, new to ℤ)
    // transfers — its ring proof having itself transferred group.invInvolution
    // through ring's AdditiveGroup model, re-materialized here.
    ctx.okSilent(&.{ "check", "std/integer-ring-model.bpa" });

    // the set theory (std/set.bpa): the membership axioms + extensionality, and
    // the 19 set-algebra identities (idempotence, identity, associativity,
    // commutativity, distributivity, De Morgan, difference laws) proved from them
    // by the extensionality→unfold→tautology recipe. Available for a structure to
    // `model` and inherit. The AATA transcription (aata/1.2.1-sets.md) aliases these.
    ctx.okSilent(&.{ "check", "std/set.bpa" });

    // collections (std/collection.bpa): sets of sets, one level up. A Collection MODELS
    // std/set.bpa with set.Element -> Set, set.Set -> Collection, so the whole set
    // algebra transfers onto collections for free (contains = member one level up).
    // Plus the CROSS-LEVEL operations set.bpa lacks — bigUnion/bigIntersection
    // (collapse a collection to a set), a universe, and the partition apparatus
    // (covers / pairwiseDisjoint / isPartition) a quotient needs.
    ctx.okSilent(&.{ "check", "std/collection.bpa" });

    // the function theory (std/function.bpa): axioms only, no theorems — a
    // declarations-only DEPENDENCY. A direct check has nothing to prove, which is
    // the correct outcome: an informational note, exit 0 (NOT a warning — the
    // warning is reserved for a file that DECLARES theorems but proves none).
    ctx.ok(&.{ "check", "std/function.bpa" },
        \\OK: 16 declarations, 0 theorems proven
        \\  — note: no theorems to check (a declarations-only file: axioms/defs/schemas — a dependency, not a proof file).
        \\
    );

    // invertible functions form a GROUP (std/function-invertible.bpa): the bijections
    // of a set under composition. A GUARDED model of std/group.bpa (guard = invertible)
    // — the group axioms proved on invertible functions (assoc/identities from funcExt;
    // inverse laws + closure under compose/inverse), then the group corpus (identity/
    // inverse uniqueness, involution, cancellation) transfers onto them for free.
    // Exercises cross-sort guarded weakening (group.Grp -> Fn where invertible).
    ctx.okSilent(&.{ "check", "std/function-invertible.bpa" });
}
