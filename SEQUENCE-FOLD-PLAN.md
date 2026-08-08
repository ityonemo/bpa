# Abstract Seq + Fold, integer-sequence models it (branch abstract-sequence-fold)

Working plan for #143. NOT part of the shipped library — delete when the branch lands.
`main` @ f9dc253 (pushed) is the rollback point.

## Goal
Split std/integer-sequence.bpa into (a) NEW abstract std/sequence.bpa (bare Seq +
a Fold layer) and (b) integer-sequence.bpa as the CALLER that MODELS the fold to
get productUpTo, keeping all the divisibility/number theory. This makes
`sequence`/`fold` a reusable abstraction any monoid can model (ℤ now; ℝ/ℚ later).

## Design principle that got us here
A subdomain file earns its own file when there's a coherent body of the main
domain's theorems provable BEFORE it and WITHOUT it (user's rule). Sequences
qualify (all of ℤ/ring/order develops with no notion of a sequence). Within the
sequence file, "facts should only deal with INDEXING" — value-specific facts
(does_divide) belong to the caller, not the abstract theory.

## The obstruction and its resolution (VALIDATED with probes — all were strict-green)
A naive "index=Nat, value=Int as two distinct sorts" split FAILS: the FTA's
σ-permutation is a Seq whose ENTRIES ARE INDICES — `at(s,i) = at(t, at(sigma,i))`
uses at(sigma,i) as BOTH a value AND an index. One monomorphic `at` can't return
Nat-for-indexing and Int-for-values at once.

RESOLUTION (user's design):
- A sequence is honestly ℕ-INDEXED (index = peano.Nat in the abstract theory).
  That is non-negotiable — a sequence is an ℕ-indexed family.
- The ℤ model OVERLOADS the abstract index sort onto nonneg(ℤ):
  `seq.Nat: NonNegZ` where `NonNegZ = integer.NonNeg = Int where nonneg`.
  Sound because nonneg(ℤ) IS a Peano model (the NonNegInt model in std/integer.bpa,
  proved earlier this branch). This is guard-INTRODUCTION on a sort overload —
  EXISTING machinery (like group.Grp: GrpH). Supply nonneg-closure facts
  (integer.nonnegZero, integer.nonnegSucc) so the injected guard discharges.
- `seq.Value: Int`. So on the ℤ side index and value BOTH sit on the Int carrier;
  the index is the nonneg refinement. Values stay Int → the FTA's ℤ arithmetic
  (~729 sub/neg sites) is UNTOUCHED. This is NOT a Nat retype of the FTA.
- Value-as-index sites `at(t, at(sigma,i))` typecheck because NonNegZ ⊂ Int and the
  nonneg TCC discharges from an in-scope hypothesis — the σ-invariant ALREADY
  carries is_nonneg(at(sigma,i)). (`is_nonneg`/`nonneg`/`NonNegZ` all resolve to the
  same integer.nonneg predicate — verified via `bpa query whereis`.)

Probes that validated this (were in /tmp, now gone — re-create if needed):
- abstract ℕ-indexed seq+fold with a fold theorem → green.
- ℤ model with `seq.Nat: NonNegZ` overload transferring the fold theorem → green
  (needs nonneg closure facts in scope for the guard).
- `at(t, at(sigma,i))` with nonneg-from-hypothesis (the exact σ shape) → green.
- a two-distinct-abstract-sorts model mapping both to Int → green (non-injective
  sort map is allowed) — but we do NOT use that; index is honestly Nat, overloaded.

## Stages (commit each on the branch even if later ones are broken)
S1 [DONE, committed fe180c9 + 699539e]: std/sequence.bpa — abstract, ℕ-indexed
   (index=peano.Nat), abstract Value, at: Seq×Nat→Value, IDENTITY/combine/foldUpTo +
   recursion axioms + fold-structure theorems + entry-graph existence axioms. Green.
S2 [NEXT]: convert std/integer-sequence.bpa to CALLER:
   - own `sort Seq`, `func at(s: Seq, i: NonNegZ): Int`, `func productUpTo(s: Seq,
     k: NonNegZ): Int` + ℤ recursion axioms (productZero=ONE, productSucc=mul).
   - `model IntSeq { seq.Nat: NonNegZ, seq.Value: Int, seq.Seq: Seq, seq.at: at,
     seq.IDENTITY: ONE, seq.combine: mul, seq.foldUpTo: productUpTo, seq.foldZero:
     productZero, seq.foldSucc: productSucc }` + nonneg closure facts in scope.
   - transfer the fold theorems onto productUpTo-statements (nonneg-relativized — OK).
   - KEEP the does_divide corpus (everyEntryDividesProduct, lastEntryDividesProduct,
     memberDividesProduct, dividesTransitive, dividesSubtracts, divisorAtMost,
     primeFactorExists, order/division re-export aliases), retyping index binders to
     NonNegZ, discharging nonneg-at-index TCCs from in-scope is_nonneg (NOT weakening).
   - std stack strict-green.
S3: aata/2.3-primes.md — retype sequence-index binders Int→NonNegZ; values stay Int;
   ℤ arithmetic untouched; discharge value-as-index nonneg TCCs from the σ-invariant.
S4: gates (add std/sequence.bpa to test_cli fmt list; fix test_std) + fmt + zig build
   test + full corpus sweep (except examples/incorrect.bpa, intentional-fail).

## STATUS: S1 committed & green. S2 partial WIP is in `git stash@{0}` (agent stopped
## mid-conversion; it still checked green but was incomplete). Corpus green at 699539e.
