# Sort-agnostic arithmetic accelerant — pure-ℤ engine, theory-supplied nonnegativity

## Why

Today `src/accelerant/arithmetic/presburger.zig` is a **ℕ-only** Presburger engine.
It resolves `add`/`succ`/`mul`/`ZERO`/`less_than` by name (so it happens to run on any
theory that exposes those), but it hardwires two ℕ-specific assumptions that make it
unsound and inexpressive for other domains:

1. **Every variable carries an implicit `≥ 0`.** Both the free-variable closure in
   `runSat` (presburger.zig:264) and quantifier compilation in `formula`
   (presburger.zig:516–527) inject `x ≥ 0` for every variable. For a genuinely-ℤ (or
   ℚ) variable this is FALSE — the engine would "prove" goals that only hold for
   nonnegative values.
2. **It keys off a hardcoded `nat` sort.** `linearOf` (406–407) and `formula`
   (499–500) reject any variable/binder whose sort isn't `symbols.nat`. So it cannot
   serve ℚ at all, and it treats "which domain" as a sort identity rather than a set of
   declared operations/facts.

It also lacks `neg`/`sub`/`prev`, so `sub(add(a,b),b) = a` — a QF-linear ℤ identity —
is rejected as out-of-fragment, forcing hand-proved cancellation lemmas.

The concrete trigger: the ℤ Euclidean-gcd port (`std/integer-divides.bpa`) needs
`sub`-cancellation steps that are textbook linear arithmetic but currently un-decidable
by the accelerant.

## The principle (user ruling)

**The engine is sort-agnostic. It never inspects a variable's sort to decide
soundness.** Deciding what is true of a theory's variables is the *theory's* job, not
the engine's. The engine offers a fixed vocabulary of well-known **symbols** and
well-known **predicates/cites**; a theory opts into the accelerant by binding its own
symbols to that vocabulary and by *supplying* — as ordinary hypotheses/cites — the
domain facts (like nonnegativity) that hold for it.

Consequences:
- **No `nat: ?SortId` sort filter.** A term is a *variable* iff it is not one of the
  bound well-known symbols. Variables are opaque linear unknowns ranging over ℤ.
- **The engine is pure Presburger-over-ℤ.** No implicit `≥ 0`. Cooper QE runs over
  unconstrained integer variables.
- **Nonnegativity is theory-supplied.** ℕ (peano) declares "my variables are `≥ 0`";
  the *elaborator*, for an `arithmetic(peano)` step, conjoins the nonnegativity atom
  (`is_nonneg(x)` / `0 ≤ x`) into the goal per bound variable before handing it to the
  engine. ℤ (integer) declares no such thing. ℚ (rational) declares neither succ/prev
  discreteness nor nonnegativity → the same engine serves it (dense case) for the
  linear fragment.
- **Well-known predicates, not just funcs.** `is_nonneg`/`less_than` are well-known
  *predicates* the theory may bind; when present the engine reads them as the linear
  atoms `x ≥ 0` / `a < b`. This is the channel through which a theory supplies domain
  facts.
- **Integrality is a declared capability, not a sort.** Whether Cooper's `div`/`mod`
  (integer) reasoning applies vs. dense (ℚ) elimination is selected by a theory-declared
  capability (the presence of a discreteness witness such as `succ`/`prev`), NOT by
  sniffing a sort. (Dense-ℚ QE is future work; the QF-linear path serves ℚ today.)

## Fragment dispatch (one engine, capability-profiled)

At entry the driver inspects which well-known symbols/preds the (bound) theory provides
and what shape the goal has, then routes to the cheapest sufficient (analysis,
certifier) pair:

- **QF-linear** (no quantifier alternation needing QE) → linear-form + validity check
  (negate goal, check unsat). Certificate: the equation/order/Farkas certifiers already
  in `arithmetic.zig`. **This is where `sub(add(a,b),b)=a` and the gcd port's sub steps
  land** — the simplest, most certifiable fragment, and it needs NO witness
  construction and NO nonnegativity.
- **Discrete-ℤ with quantifiers** → Cooper QE over ℤ (the existing engine, minus the
  implicit `≥0`). ℕ goals reach here already carrying their theory-injected `x≥0`
  hypotheses, so they decide exactly as before. Certificate: the existing Cooper replay.
- **Dense-ℚ with quantifiers** → Fourier–Motzkin / dense QE. FUTURE — not built now;
  refuse (honestly) until it exists.

## What changes (scoped to this branch: QF-ℤ + the guard move)

The full quantified-ℤ / dense-ℚ story is large. This branch does the **sound core**
that unblocks the gcd port and establishes the contract, and explicitly defers the rest.

### Engine (`presburger.zig`) — make it sort-blind + ℤ-aware

- **`Symbols`**: drop the *soundness* role of `nat` (keep an optional discreteness
  marker only for QE-mode selection, keyed off `succ`/`prev` presence — not a sort
  filter). Add `neg`, `sub`, `prev`.
- **`linearOf`** (403–445): recognize a variable by "not a well-known symbol" rather
  than by sort (remove the `v.sort != nat` reject at 406–407). Add:
  - `neg(x)` → `negated(linearOf x)`
  - `sub(a,b)` → `combine(linearOf a, -1, linearOf b)`
  - `prev(x)` → `shifted(linearOf x, -1)`
  (`negated`/`combine`/`shifted` already exist and carry negative coeffs.)
- **Remove the implicit `≥0` injection** at the free-var closure (264), `runTrace`
  (305–308), and `formula` quantifier compilation (516–527). Quantifier binders compile
  to `exists x; body` / `forall x; body` with NO guard. Remove the `q.sort != nat`
  reject at 499–500.
- The internal `Linear`/`Formula`/Cooper QE already operate over ℤ with negative
  coefficients — **no change** to the elimination core, the `Replay` struct, or
  `cooperTraced`.

### Elaborator (`arithmetic.zig`) — theory supplies nonnegativity

- **`arithmeticSymbols`** (497): also resolve `neg`/`sub`/`prev` and the well-known
  nonnegativity predicate via `wellKnownSym` against the theory scope (the
  `arithmetic(<mod>)` `theory_file` mechanism already exists, elaborate.zig:2804).
- **Nonnegativity injection — the mechanism (settled)**: a well-known **nonnegativity
  predicate** (`nonneg`, resolved by name via `wellKnownSym` against the theory scope)
  is added to `Symbols`. **Its presence in scope IS the injection request.** If the
  theory binds `nonneg` over the arithmetic sort, the elaborator conjoins `nonneg(x)`
  per bound variable; if it binds none (pure ℤ/ℚ), it injects nothing. No sort sniff, no
  capability bit — the predicate's presence is the whole signal.
  - The universal-prefix stripper (1557–1568) — which already opens each `forall x`
    binder as a fixed-but-arbitrary fvar — additionally conjoins `nonneg(x)` into the
    premise set for each stripped binder when `symbols.nonneg != null`. Inner
    `exists`/`forall` binders over the same sort are likewise guarded before hand-off
    (this is the moved-out version of the engine's old 264/308/516–527 injection —
    now done in the elaborator, gated on the bound predicate).
  - `peano` binds `nonneg` → ℕ variables get `x≥0`, existing Cooper proofs unchanged.
    `integer` binds NO nonneg into its arithmetic vocabulary (it has `nonneg` the pred,
    but does not wire it as the arithmetic well-known nonneg) → ℤ variables unconstrained.
    The abstract `sort Nat` test fixtures gain a `pred nonneg(n: Nat)` so they keep ℕ
    semantics; the ℤ fixture binds none.
  - **Engine reads `nonneg(x)` as the linear atom `x ≥ 0`** wherever it appears as a
    hypothesis/conjunct (so an injected `nonneg(x)` compiles to the same `≥0` the engine
    used to add itself). This is the well-known-predicate channel.

### Witness construction (deferred beyond QF)

`buildWitness`/`witnessCandidates` (arithmetic.zig:760–783, 941–956) build `succ`-tower
(nonnegative) witnesses. For QF-ℤ there are no existentials to witness, so **no change
needed now**. Quantified-ℤ goals whose witnesses are negative need `neg`/`prev`
construction — DEFERRED with the quantified-ℤ tail. ℕ quantified goals keep nonnegative
witnesses (they carry `x≥0`), so the existing Cooper tests stay green.

## Verification (fractal RED→GREEN)

- **RED**: a fixture `tests/cases/arithmetic_integer_sub.bpa` with
  `theorem t: forall a, b: Int; sub(add(a, b), b) = a proof … [by arithmetic(integer)]`
  — today errors "sub(add(a,b),b) is outside linear arithmetic".
- **GREEN**: after the change, `[by arithmetic(integer)]` decides it (strict, with a
  kernel certificate via the equation certifier). Add the eight sub/add cancellation
  identities as a gate to exercise neg/sub/prev in every position.
- **No regression** (the load-bearing check): the ENTIRE existing arithmetic gate set
  (`tests/test_tactics.zig:355–474` — arithmetic/farkas/cooper/smt fixtures) stays
  green with identical golden output. Especially `cooper_witness`/`cooper_parity` (ℕ
  quantified induction) — they must still decide + certify, now via theory-injected
  `x≥0` rather than engine-implicit. And the whole std/aata corpus (peano, FTA) re-checks
  unchanged: `zig build test` fully green.
- **Soundness canary**: a fixture asserting a ℕ-only-true goal over ℤ (e.g.
  `forall x: Int; is_nonneg(sub(x, ONE))` or `forall x: Int; less_than(ZERO, succ(x))`
  WITHOUT a nonneg hypothesis) must now be REJECTED with a countermodel (x = -1),
  proving the implicit `≥0` is truly gone.

## Critical files
- `src/accelerant/arithmetic/presburger.zig` — engine: `Symbols`, `linearOf`, the 8
  nonnegativity sites (139–143, 264, 305–308, 406–407, 499–500, 516–527).
- `src/accelerant/arithmetic.zig` — driver: `arithmeticSymbols` (497), the
  universal-prefix stripper + nonneg injection (1557–1568), certifier chain (unchanged
  for QF).
- `src/elaborate.zig` — `wellKnownSym`/`theoryScope` (2804, 3508) — the theory-binding
  channel new symbols/preds resolve through.
- `std/peano.bpa` / `std/integer.bpa` — the theory bindings that declare (or don't)
  domain nonnegativity + bind neg/sub/prev.
- `tests/test_tactics.zig` + `tests/cases/arithmetic*/farkas*/cooper*/smt*` — the
  no-regression surface.

## Deferred (explicitly out of scope for this branch)
- Dense-ℚ quantifier elimination (Fourier–Motzkin) — the ℚ quantified case.
- Negative-witness construction for quantified-ℤ existentials.
- Broad corpus migration of hand-proved sub/cancellation lemmas to `[by arithmetic]`
  (do the gcd port's own steps; sweep the rest later).
