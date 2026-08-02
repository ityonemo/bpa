# ISA-EXPLORATION.md — structure reuse ("X is-a Y")

Branch `isa-structure-reuse`. Exploration, not committed to `main` behavior.
Motivating case: **nonneg-ℤ is-a Peano ℕ** — the nonnegative integers, with ℤ's
`ZERO`/`succ`/`add`/`mul` restricted to `nonneg`, satisfy the Peano axioms. If we
could express that, the entire `std/peano-*.bpa` theorem corpus would transfer to
nonneg-ℤ for free — instead of re-proving the ℕ algebra over ℤ by hand (exactly
what `std/integer-ring.bpa` has been doing).

## What the transfer actually requires (the concrete obstruction)

For nonneg-ℤ to "be" a Peano ℕ, ℤ's symbols must satisfy the 7 Peano axioms
(std/peano.bpa) under the map `Nat ↦ Int-guarded-by-nonneg`:

| Peano axiom | over ℤ (std/integer.bpa + ring) | note |
|---|---|---|
| `succInjective` | holds globally (from prevSucc) | ✅ |
| `succNotZero`   | FALSE globally (succ(prev 0)=0); TRUE on `nonneg` | ⚠️ **needs the guard** |
| `addZeroLeft`   | proven (integer-ring) | ✅ |
| `addSuccLeft`   | proven (integer-ring) | ✅ |
| `mulZeroLeft`   | proven (integer-ring) | ✅ |
| `mulSuccLeft`   | proven (integer-ring) | ✅ |
| `oneIsSuccZero` | same axiom | ✅ |
| `induction` (over Nat) | ℤ's `nonnegInduction` (over nonneg Int) | ⚠️ relativized form |

So TWO things differ, and they are the whole problem:

1. **Carrier relativization.** A ℕ theorem `∀n: Nat; P(n)` must become
   `∀n: Int; nonneg(n) → P(n)`. Every ℕ-quantifier picks up a `nonneg` guard.
2. **A guarded axiom.** `succNotZero` holds only on nonnegatives; ℕ uses it
   unconditionally. So the transfer must *discharge* each Peano axiom **as it
   holds over the target** — some globally, `succNotZero` only under `nonneg`.

This is precisely a **structure INTERPRETATION** (Isabelle locale interpretation
/ Coq module functor): map ℕ's symbols to ℤ's, prove the axioms hold (relativized),
inherit every theorem (relativized).

## What bpa already has (and where it stops)

- **Schema / `instantiate`** (`ast.SchemaParam = {name, arg_sorts, result}`)
  parameterizes over a **term/predicate of a signature** — e.g.
  `induction(prop: Nat -> Prop)`. It does NOT parameterize over a **sort**. So it
  can abstract "a predicate on Nat" but not "which sort plays Nat." That is the
  one-level-short gap.
- **Sort aliasing** (`sort X = other.Y`, elaborate.zig:217) is real *identity* —
  works only when the carriers are literally the same sort. ℤ and ℕ are distinct
  sorts, so aliasing does NOT apply here (nonneg-ℤ is a *guarded subdomain* of a
  *different* sort, not the same sort as Nat).
- **Guarded application** (`func div(a,b) requires b != ZERO`) already attaches a
  proof obligation to a symbol — the machinery for "carries an obligation" exists.

## Candidate mechanisms (compare against nonneg-ℤ is-a ℕ)

1. **Interpretation / instantiation of a parameterized theory.** Make `std/peano`
   a `theory Peano(Nat: sort, ZERO, succ, add, mul, ...)` (sort + symbol params);
   INSTANTIATE at `(Int, ZERO_ℤ, succ_ℤ, ...)` discharging the 7 axioms (relativized
   to nonneg). All ℕ theorems transfer, symbols renamed, quantifiers relativized.
   - Pro: the "real" answer; general (works for monoid/order/ring reuse too).
   - Con: needs SORT parameters (schema machinery lacks them) + automatic
     quantifier relativization on transferred theorems + axiom-obligation
     discharge. Largest.

2. **Subtyping / `isa`.** Declare `NonnegInt isa Nat` (a coercion between a guarded
   subdomain and Nat), let Nat-typed theorems apply to nonneg-ℤ terms, WITH the
   guard discharged.
   - Pro: lighter surface; "X is-a Y" reads naturally.
   - Con: still needs the relativization + `succNotZero` guard; subtyping between
     a *guarded subset of Int* and *Nat* is really interpretation in disguise.

3. **Scoped/local unification.** "For this theorem, treat Nat as Int-under-nonneg."
   A hypothesis-like identification scoped to a proof, discharged out.
   - Pro: most bpa-idiomatic (like `assume`/`hole`); no global commitment.
   - Con: transfers ONE theorem at a time, not the whole corpus; still needs the
     relativization machinery. Good for one-off reuse, weak for library-scale.

## Open questions to probe next

- Can we prototype the transfer of ONE ℕ theorem to nonneg-ℤ **by hand today**
  (declare the Peano axioms as nonneg-guarded theorems over ℤ, then... there is no
  way to cite the ℕ *proof* — only re-run it)? Writing that manual transfer shows
  exactly what a mechanism automates.
- Does relativization compose (a ℕ theorem citing another ℕ theorem — both must
  relativize consistently)?
- Is the minimal useful thing "sort parameters on schemas" (extend the existing
  machinery by one axis) rather than a whole new interpretation construct?

No decision yet — this doc records the terrain.
