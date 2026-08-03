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

    // the integers ℤ ring algebra (std/integer-ring.bpa): left/right recursion,
    // commutativity, associativity, the additive-inverse law n+(-n)=0, and the
    // mul lemmas — all proven from the ℤ axioms by bidirectional induction.
    ctx.ok(&.{ "check", "std/integer-ring.bpa" }, "OK: 59 declarations, 16 theorems proven\n");

    // ℤ subtraction (total: a-b = a+(-b)) + the strict order, over the ring
    // algebra: subSelf (a-a=0) and subAddCancel ((a-b)+b=a), proven with no
    // induction from the inverse law; order via less_than intro/elim.
    ctx.ok(&.{ "check", "std/integer-order.bpa" }, "OK: 83 declarations, 18 theorems proven\n");

    // abstract divisibility (std/divisibility.bpa): a carrier with mul/add/ONE
    // and the divides predicate; dividesRefl/dividesMul/dividesAdd proved once,
    // over the abstract carrier. ℕ and ℤ `model` this to inherit them.
    ctx.ok(&.{ "check", "std/divisibility.bpa" }, "OK: 13 declarations, 3 theorems proven\n");

    // ℤ divisibility + powers (std/integer-divides.bpa): `divides` intro/elim +
    // pow recursion; the three basic facts (refl/mul/add) TRANSFER from the
    // abstract divisibility theory via `model IntegerDivisibility`.
    ctx.ok(&.{ "check", "std/integer-divides.bpa" }, "OK: 103 declarations, 22 theorems proven\n");

    // the group theory (std/group.bpa): the 5 group axioms + an opt-in
    // `opCommutative`, and the 10 basic-property theorems (identityUnique,
    // inverseUnique, invProduct, cancelLeft, …) proved from the axioms alone.
    // The AATA transcription (aata/3.2-groups.md) aliases these under book
    // notation; the checked proofs live here.
    ctx.ok(&.{ "check", "std/group.bpa" }, "OK: 20 declarations, 10 theorems proven\n");

    // group powers (std/group-power.bpa): g^n over a Nat exponent, layered over
    // std/group.bpa + std/peano.bpa (keeping the core group theory import-free).
    // Defines pow(g,n) recursively and proves the exponent-addition law
    // powAdd: pow(g, m+n) = op(pow(g,m), pow(g,n)) by induction on n.
    ctx.ok(&.{ "check", "std/group-power.bpa" }, "OK: 87 declarations, 28 theorems proven\n");

    // the ring theory (std/ring.bpa): an additive abelian group + associative,
    // distributing multiplication. Its additive half MODELS std/group.bpa (a
    // TWO-LEVEL structure — a model inside a modelable theory). Judson's first
    // ring proposition (a·0=0·a=0; a(-b)=(-a)b=-(ab); (-a)(-b)=ab) is proved by
    // TRANSFERRING the additive-group cancelRight/inverseUnique/invInvolution
    // through the AdditiveGroup model rather than re-deriving them. (15 = the
    // imported group corpus (10) + ring's 5 elementary theorems; the synthetic
    // materialized theorems are suppressed.)
    ctx.ok(&.{ "check", "std/ring.bpa" }, "OK: 42 declarations, 15 theorems proven\n");

    // ℤ as a thin model of the ring theory (std/integer-ring-model.bpa): the
    // THREE-LEVEL chain ℤ → ring → group. `model IntegerRing = Int` discharges
    // ring's 9 axioms from ℤ's facts (associativity axioms now bind the canonical
    // a,b,c order, so ℤ's assoc theorems α-match the remapped ring axioms directly
    // — no binder-order adapters needed), and negMulNeg ((-a)(-b)=ab, new to ℤ)
    // transfers — its ring proof having itself transferred group.invInvolution
    // through ring's AdditiveGroup model, re-materialized here.
    ctx.ok(&.{ "check", "std/integer-ring-model.bpa" }, "OK: 121 declarations, 32 theorems proven\n");

    // the set theory (std/set.bpa): the membership axioms + extensionality, and
    // the 19 set-algebra identities (idempotence, identity, associativity,
    // commutativity, distributivity, De Morgan, difference laws) proved from them
    // by the extensionality→unfold→tautology recipe. Available for a structure to
    // `model` and inherit. The AATA transcription (aata/1.2.1-sets.md) aliases these.
    ctx.ok(&.{ "check", "std/set.bpa" }, "OK: 35 declarations, 19 theorems proven\n");

    // the function theory (std/function.bpa): axioms only, no theorems — a
    // direct check materializes nothing and exits nonzero with a warning.
    ctx.okCode(&.{ "check", "std/function.bpa" },
        \\OK: 17 declarations, 0 theorems proven
        \\  — WARNING: 0 theorems proven — nothing was checked (a schema/axiom/declarations-only file proves nothing on its own).
        \\
    , 1);
}
