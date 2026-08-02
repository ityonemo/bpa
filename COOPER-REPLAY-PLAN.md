# COOPER-REPLAY-PLAN.md — general Cooper-QE-replay certificates

## STATUS (2026-08-01): LANDED — all three layers

All three layers are built and green:
- **Layer 1** (`2dd2b09`): trace-emitting Cooper engine (`presburger.trace` →
  `Replay`; `cooperTraced` shares the `prepared` prelude with `cooper`).
- **Layer 2** (`cc0d965`): the `cooper` certifier link, period-1 witness
  direction (`tests/cases/cooper_witness.bpa`, kernel-checked in default mode).
- **Layer 3**: induction synthesis (`cooperInduction` in `elaborate.zig`) —
  period-D goals certify via a synthesized induction. `tests/cases/cooper_
  parity.bpa` and the target `examples/peano.bpa` `evenOrOdd` both check ELABORATED in
  default mode (`OK: 18 declarations, 6 theorems proven`, no accelerated steps).

Declared boundaries (the `cooper` link declines these → `--fast`): multi-fixed-
variable goals, and nested/deeper alternation (`∀∃∀`). The witness search is a
bounded shift-table (constant towers + IH-witness towers) — sufficient for the
parity family and period ≤ small; a goal needing an unlisted witness declines
cleanly rather than emitting an unsound proof. The rest of this document is the
original design, kept for the layer detail.

## 0. Summary and non-goals

**Goal.** Make `by arithmetic` goals with quantifier alternation (∀∃) certify ELABORATED — emit ordinary kernel steps instead of an accelerated verdict — so `bpa check` in **default mode** accepts them. Canonical target: `examples/peano.bpa:182`

```
theorem evenOrOdd: forall x: Nat; exists y: Nat; x = add(y, y) or x = succ(add(y, y))
```

which today fails default mode with (verified live):

```
examples/peano.bpa:182:9: error: 'arithmetic' is valid but no certifier could prove it here:
  - equation/order/exists: form not in certification scope
  - mixed-skeleton: form not in certification scope
  - farkas: theory lacks symbol 'less_than'
use --fast to accept the accelerated verdict
```

and passes under `--fast` (accelerated: `1 accelerated: arithmetic`).

The delivered work is a **fourth peer certifier link** — `cooper` — in the `certifiers` array (`src/elaborate.zig:3647`), exactly where the comment at `3644-3646` anticipates it, built as three layers with a kernel-checked `.bpa` fixture per replay scope, RED-first.

**Non-goals (explicit).**
- **Nonlinear** (`mul(x,y)` both variable): undecidable, no complete certifier — see `NONLINEAR-PLAN.md`. The Cooper link *declines* (`out_of_scope`) whenever `presburger.outOfFragment` flags the goal; the engine already rejects it at `linearOf` (`src/presburger.zig:324-330`).
- **Anything already certified**: QF-linear equation/order (`equationCertifier`), the const-witness existential (`ExistsCert`), mixed-skeleton, and Farkas infeasibility. The chain is first-`certified`-wins; `cooper` runs LAST, so it only sees goals the cheaper links declined. It must not regress them.
- The **positive-conclusion linear-order gap** (`CERTIFICATES-PLAN.md:31-49`) — quantifier-free, a separate near-term link, not Cooper.
- The mode machinery (`--fast`/`--pure`, accelerated disclosure, summary) is **done** (`CERTIFICATES-PLAN.md:3-15`); this plan only adds coverage.

---

## 1. Architecture decision: where the trace lives

The Cooper engine (`src/presburger.zig:601 cooper`) builds `OR_{j=1..D}( F₋∞(j) OR OR_{b∈B} F(b+j) )`, evaluates it with `evalGround` (`631`), and **discards it** — `decide()` returns only a `Verdict` (`43-57`). Nothing about the elimination is recoverable today.

**Decision (mirrors `src/farkas.zig`):** do NOT thread emit-state through `presburger.zig`. Instead:

1. Add a **pure trace-emitting variant** in `presburger.zig` that RECORDS the elimination data into a plain-old-data `Replay` struct (no term pool, no kernel — same discipline as `farkas.zig`, whose header says "no term pool, no elaborator, no kernel; nodes are opaque"). The existing `decide()`/`satisfiable()`/`inFragment` and all 9 unit tests are **untouched** — they keep calling `runSat`→`eliminate`→`cooper` exactly as now.
2. The certifier link in `elaborate.zig` calls the new `Ctx.trace(...)` entry, gets the `Replay`, and does ALL term-pool/kernel work (mirroring how `farkasCertificate` at `elaborate.zig:3678` consumes `farkas.refute`'s opaque `Refutation`).

This keeps the trusted-engine surface (`presburger.zig:1-19` header) stable and the emit logic where the pool lives.

---

## LAYER 1 — trace-emitting Cooper engine

### 1.1 The trace data structure (new, in `presburger.zig`)

The certifier needs, for the single ∃-variable `y` being eliminated (evenOrOdd has exactly one existential; see §3.3 for multi-∃), the exact disjunction Cooper built so it can (a) pick a witness per disjunct for the ⟸ direction and (b) recover the residue-class structure for the ⟹ direction:

```zig
// exported from presburger.zig, PURE (i128 + slices, no TermId)
pub const Replay = struct {
    /// coefficient LCM δ from coefficientLcm (presburger.zig:465); y = δ·x
    delta: i128,
    /// period D = modulusLcm of the normalized+stride formula (511, used at 609)
    period: i128,
    /// boundary set B: each lower bound's base b (presburger.zig:527 boundaries)
    boundaries: []const LinearDump,
    /// per-disjunct record, in the exact build order of cooper() (618-625)
    disjuncts: []const Disjunct,
    /// free-variable name→index correspondence (Ctx.free_vars order, :168)
    free_names: []const StrId,
};
pub const Disjunct = union(enum) {
    /// the −∞ residue at offset j (substInf, presburger.zig:577); j in 1..D
    minus_inf: struct { j: i128 },
    /// the boundary probe: witness y := b + j (subst, presburger.zig:550)
    boundary: struct { b_index: usize, j: i128 },
};
pub const LinearDump = struct { coeffs: []const i128, konst: i128 };
```

`LinearDump` is the certifier-visible echo of the internal `Linear` (`presburger.zig:132`). The certifier maps a `LinearDump` back to a `TermId` by reading `coeffs` against the free-variable index map — which is the `Ctx.free_vars` order (`presburger.zig:168`), exported as `free_names`.

### 1.2 The producing entry point

Add a sibling to `decide()`:

```zig
pub fn trace(arena, pool, symbols, premises, goal) Allocator.Error!union(enum){
    replay: Replay,          // goal is `forall x…; exists y; body`, valid, traced
    not_applicable,          // shape not ∀…∃… over Nat, or out of fragment
    verdict: Verdict,        // decided but not the replay shape (declines upstream)
}
```

Internally it reuses the existing compilation (`formula`, `linearOf`) but calls a **traced clone** of `cooper` — `cooperTraced(v, f, *Replay)` — byte-for-byte the loop at `presburger.zig:617-626` with `try replay.disjuncts.append(...)` inserted at each `substInf`/`subst`, recording `delta`/`period`/`boundaries` at `602-613`. The original `cooper` is NOT modified. To avoid drift, factor the shared numeric prelude (`coefficientLcm`→`normalized`→`stride`→`modulusLcm`→`boundaries`) into one helper `prepared(v, f) -> struct{ g, delta, period, lows }` that BOTH `cooper` and `cooperTraced` call; the only divergence is that `cooperTraced` records instead of folding into a `.disj` node. Safe refactor: `cooper`'s behavior is preserved because `prepared` returns the same intermediates.

**Scope of layer 1 for evenOrOdd:** the goal is `∀x ∃y ( x = 2y ∨ x = 2y+1 )`. After the ∀x strip, the certifier hands `presburger.trace` the single-∃ goal `∃y ( x = 2y ∨ x = 2y+1 )` with `x` free. Cooper on `y`: `2y` has coeff 2, so `delta = 2`, the stride atom `2 | y` gives `period = 2`, `D = 2`, boundary set from the equalities' compiled `≥` atoms. The `Replay` records D=2 and the two residue classes — precisely the parity structure layer 3 turns into `induction`.

### 1.3 Keeping the engine green

- No signature change to `decide`/`satisfiable`/`inFragment`/`outOfFragment` (`presburger.zig:73-128`).
- The 9 unit tests at `presburger.zig:748-839` (including `"every number is even or odd"` at `769`) still pass — they call `decide`, which never touches `trace`/`cooperTraced`.
- **New layer-1 unit tests** (RED first): `trace` on the evenOrOdd body returns `.replay` with `delta == 2`, `period == 2`; `trace` on a nonlinear goal returns `.not_applicable`; `trace` on `∀a,b; a<a+succ(b)` (no ∃) returns `.not_applicable`. `zig build test` green.

**Layer-1 has no `.bpa` fixture** — it emits no kernel steps yet. Its RED gate is the new presburger unit tests. The first *kernel-checked `.bpa`* fixture arrives in layer 2.

---

## LAYER 2 — witness direction (⟸), the easy half, shipped first

### 2.1 What it proves and why it is complete alone

The Cooper disjunction `⋁ᵢ Dᵢ ⟹ ∃y.F(y)` is the trivial direction: each disjunct `Dᵢ` names a concrete witness value for `y` (a boundary probe `y := b+j`, or the −∞ residue's representative), and `F(witness)` holds. GIVEN the disjunction as a hypothesis, `∃y.F` follows by `or_elim` over the disjuncts, each arm discharged by `exists_intro(witness)`.

But layer 2 cannot yet PRODUCE the disjunction as a proven step — that is layer 3 (⟹). So layer 2 ships the sub-scope where Cooper's disjunction collapses to a SINGLE witness with NO periodicity obligation — a `D = 1`, single-boundary replay — so the ⟸ emit is exercised end-to-end without the ⟹ induction. Layer-2 RED fixture (`tests/cases/cooper_witness.bpa`):

```
theorem existsPredecessorOrZero: forall x: Nat; exists y: Nat; x = y or x = succ(y)
```

Cooper eliminates `y` with `delta = 1`, `period = 1`, one boundary; the residue is trivially true, so the disjunction is a tautology and the ⟸ step is `exists_intro(x)` in one arm — kernel-checked, no induction. Currently falls to the terminal; after layer 2 certifies with every step kernel-checked in default mode.

### 2.2 The emit (references verified)

The witness-assembly reuses the existing existential emit template at `elaborate.zig:2974-2978`:

```zig
.exists => |ex| blk: {
    const inner_just = try self.emitInner(low, parent, loc, ex.inner);
    const inst_ref = try self.emitStep(low, parent, loc, ex.instance, inner_just);
    break :blk .{ .exists_intro = .{ .step = inst_ref, .witness = ex.witness, .witness_loc = loc } };
},
```

- `kernel.Justification.exists_intro` = `struct { step: SRef, witness: TermId, witness_loc: u32 }` (`kernel.zig:73`), checked at `kernel.zig:406-427`: the step must claim the existential, and `body[witness]` must α-equal the cited step's formula.
- `or_elim` = `struct { disj: SRef, left: BRef, right: BRef }` (`kernel.zig:80`), checked `kernel.zig:476-506`; each arm is an `assume` block concluding the shared goal. The certifier already builds nested `or_elim` trees (`case on` fan-out at `elaborate.zig:646-705`).
- Each arm: `exists_intro(witnessᵢ)` where `witnessᵢ` is the `LinearDump`→`TermId` reconstruction (via `buildComb`/`buildTower`, `elaborate.zig:2565-2587`, to assemble `b+j` as a Nat tower/sum over the fixed variables).
- Peel ∀ prefix / fold back out exactly as `farkasCertificate` does: `newBlock(.fix …)` (`elaborate.zig:3697`), `forall_intro` fold (`3789-3796`).

### 2.3 Link registration and decline

```zig
const certifiers = [_]Certifier{
    .{ .name = "equation/order/exists", .run = &equationCertifier },
    .{ .name = "mixed-skeleton", .run = &mixedCertifier },
    .{ .name = "farkas", .run = &farkasCertificate },
    .{ .name = "cooper", .run = &cooperCertificate },   // NEW
};
```

`cooperCertificate` (new `fn`, sibling of `farkasCertificate`):
- Get `symbols`; if `symbols.nat == null` → `.declined = .out_of_scope`.
- Call `presburger.trace(...)`; on `.not_applicable`/`.verdict` → `.declined = .out_of_scope`.
- On `.replay`: if `replay.period == 1` (layer 2 scope), emit the ⟸ witness assembly, return `.certified`.
- If `replay.period > 1` (needs induction): layer 2 returns `.declined = .out_of_scope`; **layer 3 replaces this branch**.
- Missing induction axiom (layer 3) → `.declined = .{ .missing_lemma = "induction" }`, surfaced flat at the terminal.

**Layer-2 RED gate:** `tests/cases/cooper_witness.bpa` with `existsPredecessorOrZero` — fails at the certifier terminal before, `ctx.ok(&.{"check", "tests/cases/cooper_witness.bpa"}, "OK: N declarations, 1 theorems proven\n")` after (default mode, no `--fast`). Unit test: `cooperCertificate` on the fixture returns `.certified`. `zig build test` green; earlier layers unchanged.

---

## LAYER 3 — periodicity direction (⟹), the research-grade half

### 3.1 The obligation

To emit the disjunction as a PROVEN step (so layer 2's `or_elim` has something to eliminate), we must prove `∃y.F(y) ⟹ ⋁ⱼ Dⱼ` — equivalently, every satisfying `y` lands in one of the `D` residue classes. Over ℤ this is Cooper's periodicity lemma; over **Nat with the `induction` axiom** (`std/peano.bpa:72`) the only available proof is **induction on the eliminated/fixed variable**. So layer 3 SYNTHESIZES an induction and cites `induction`.

For evenOrOdd the induction is on `x`, predicate `P(k) := ∃y ( k = 2y ∨ k = 2y+1 )`, exactly the hand proof `std/peano-parity.bpa:130-132`:

```
[by instantiate induction((fun k: Nat => divides(TWO, k) or divides(TWO, succ(k)))) base-case induction-step-for-all-k]
```

(the arithmetic goal uses `∃y. k=2y ∨ k=2y+1` directly since that IS the goal body).

### 3.2 Deriving P(k), base, and step MECHANICALLY from the Replay

**Predicate.** `P(k)` is the goal body with the outer ∀-variable renamed to the induction variable `k` — the `body` returned by `peelUniversal` (`elaborate.zig:1374-1389`) with `x ↦ k`. For evenOrOdd, `P(k) = ∃y ( k = add(y,y) ∨ k = succ(add(y,y)) )`. As a `TermId`: `pool.close(body, k)` then wrap as the schema generator lambda `fun k: Nat => P(k)`.

**Base case `P(ZERO)`.** Substitute `k := ZERO`. For evenOrOdd, `∃y ( 0 = 2y ∨ 0 = 2y+1 )`, witness `y := ZERO`. This is EXACTLY the const-witness existential the existing `ExistsCert` path certifies: `presburger.trace` on `P(ZERO)` returns a `period == 1` replay → **reuse the layer-2 emitter** on the ground instance.

**Step `∀k. P(k) → P(succ(k))`.** Emit a `fix k` block, then an `assume P(k)` block (the IH), then prove `P(succ(k))` FROM `P(k)`. From a witness `y₀` for `k` (unpack the IH existential, `exists_elim`/`unpack`, `kernel.zig:74`, `428-444`), construct the witness for `succ(k)` by a **residue-class shift** read off the `Replay`:
- If `k` was in class `2y` (even), then `succ(k) = 2y+1` — same `y₀`, other disjunct arm.
- If `k` was in class `2y+1` (odd), then `succ(k) = 2(y+1)` — witness `succ(y₀)`, first arm.

This is a `case on` the IH's disjunction (`elaborate.zig:646-705` fan-out) with two arms, each an `exists_intro` of the shifted witness. The witness shift map `(class i at k) ↦ (class i' at succ(k), witness = y₀ + shiftᵢ)` is computed from `Replay.disjuncts`: period `D` residue classes rotate under `+1`, and the witness increments by `⌊(offset+1)/D⌋` when the class wraps. For `D = 2` this is the parity flip. **This shift table is the general mechanism** and is the crux of layer 3.

**Instantiation.** Build the `induction` instance and cite it. The justification is `kernel.Justification.schema_instance` = `struct { instance: TermId, premises: []const SRef }` (`kernel.zig:93`), checked at `kernel.zig:559-576`: the kernel peels the instance's implication antecedents, requiring each cited premise SRef to α-match, and the residue to match the step claim. To construct `instance`: β-reduce `induction`'s quantified `prop` at the lambda in the certifier (a local helper `instantiateInductionAxiom(prop_lambda) -> TermId` that opens `induction`'s formula and substitutes `prop`), then `.{ .schema_instance = .{ .instance, .premises = &[_]SRef{ base_ref, step_ref } } }`.

**KERNEL FACT — VERIFIED (2026-08-01).** The kernel's `schema_instance` check (`kernel.zig:559-576`) IS axiom-agnostic: it takes `r.instance` (a TermId implication chain), peels antecedents, α-matches each against a cited premise's formula (`alphaEq`), and requires the residue to equal the step claim. NO schema re-elaboration in the kernel — that lives in the elaborator (`instantiateSchema`, elaborate.zig:1189). So the certifier does NOT route through the schema machinery at all.

**Instance construction — SIMPLER than routing through `induction`.** Build the concrete instance formula DIRECTLY by term construction: with `P_closed = pool.close(goal_body, k_name)`, β-reduction is `pool.open(P_closed, arg)` (the exact primitive `elaborateCall` uses at elaborate.zig:4542). So:
```
instance = P[ZERO] -> (forall k; P[k] -> P[succ(k)]) -> forall n; P[n]
```
is assembled with `pool.open(P_closed, ZERO)`, `pool.open(P_closed, k_fvar)`, `pool.open(P_closed, succ(k_fvar))`, and `pool.open(P_closed, n_fvar)` under freshly-quantified binders — no dependence on `induction`'s stored form beyond confirming it resolves (`wellKnownFact("induction")`). Then `.{ .schema_instance = .{ .instance, .premises = &[_]SRef{ base_ref, step_ref } } }`. The kernel checks it against the claim `forall n; P[n]` by peeling the two antecedents and α-matching base_ref/step_ref.

### 3.3 The genuine unknowns / where general exceeds evenOrOdd (named, not deferred)

1. **Multi-∃ / nested alternation.** evenOrOdd has one ∃ under one ∀. A general `∀…∃…∀…` needs Cooper applied repeatedly. **Plan:** build layer 3 for **single-∃ under a ∀-prefix** (covers evenOrOdd and the parity family), and make `cooperCertificate` DECLINE (`out_of_scope`) on deeper alternation rather than emit an unsound partial proof. The one honest boundary — declared, not silent.

2. **Period D > 2.** The shift table generalizes (residue rotation), but the base case must witness ALL D classes and the step's `case on` has D arms. Combinatorial blowup bounded by `period > 4096 → too_large` (`presburger.zig:614`); keep a tighter cap (`D ≤ 16`) in `cooperCertificate`, decline above it.

3. **Non-equality boundary atoms.** A goal mixing `less_than` bounds with divisibility produces boundary probes `y := b+j` where `b` is a non-trivial linear form; each arm's leaf goal dispatches back through the existing `arithCertCore` (`elaborate.zig:2830`) — so the Cooper link COMPOSES with the QF-linear link. Risk: arm goals needing Farkas inside the induction step.

4. **The −∞ residue arm.** When a disjunct is `minus_inf`, there is no finite boundary witness; over Nat this is where induction is genuinely load-bearing. For evenOrOdd the −∞ arms are `.fls` and drop out; the GENERAL case proves the residue arm by the SAME induction predicate (subsumed, not separate). Second fixture after evenOrOdd.

### 3.4 Layer-3 fixtures (RED-first)

- **`tests/cases/cooper_parity.bpa`** — `evenOrOddArith: forall x: Nat; exists y: Nat; x = add(y, y) or x = succ(add(y, y))` with `addZeroLeft`/`addSuccLeft`/`induction` in scope. RED: certifier terminal error today; GREEN: `ctx.ok(..., "OK: … 1 theorems proven\n")` — default mode, ELABORATED.
- **`tests/cases/cooper_period3.bpa`** — a `D = 3` theorem (`x = 3y ∨ x = 3y+1 ∨ x = 3y+2`) to exercise the general shift table.
- **The real target:** `examples/peano.bpa:182` `evenOrOdd` flips from terminal error to proven with every step kernel-checked. Its `tests/test_examples.zig` golden updates from the accelerated `--fast` summary to a clean default-mode all-proven line, and the file-header comment (`examples/peano.bpa:9-12`) is corrected.

Unit test (layer 3): `cooperCertificate` on the parity replay returns `.certified` and the emitted proof passes the kernel.

---

## 4. Where the link slots in and what it declines

- **Registration:** append `.{ .name = "cooper", .run = &cooperCertificate }` to `certifiers` (`elaborate.zig:3647`), LAST. `reasons: [certifiers.len]Reason` sizing is automatic.
- **Declines (each surfaced flat at the terminal):**
  - `presburger.trace` not `.replay` → `.out_of_scope`.
  - `symbols.nat`/`succ`/`add` absent → `.{ .missing_symbol = "…" }`.
  - `induction` axiom absent → `.{ .missing_lemma = "induction" }` (via `wellKnownFact("induction", loc)`, `elaborate.zig:2486`).
  - period/alternation past the emit cap or nested-∃ → `.out_of_scope`.
- Nonlinear never reaches here — `linearOf` rejects it upstream.

---

## 5. Verification

- `zig build test` green throughout every layer; earlier layers land and stay green independently.
- **The acceptance flip:** `bpa check examples/peano.bpa` (DEFAULT, no `--fast`) goes from the `evenOrOdd:182` certifier-terminal error to `OK: N declarations, M theorems proven` with evenOrOdd **no longer in the `accelerated: arithmetic` count**.
- `--fast` still works unchanged (the terminal's `!certify_arithmetic` branch is untouched — the accelerated escape hatch for goals outside Cooper's emit scope).
- `presburger.zig`'s `decide`/`satisfiable`/`inFragment` and all 9 existing unit tests unchanged.

## 6. Layer sequence (RED-first each)

1. **Layer 1** — `Replay` struct + `trace`/`cooperTraced` in `presburger.zig`; RED = new presburger unit tests. No `.bpa` fixture.
2. **Layer 2** — `cooperCertificate` link, `period == 1` witness-⟸ emit reusing `exists_intro`/`or_elim`; RED = `tests/cases/cooper_witness.bpa` (`existsPredecessorOrZero`) failing → passing with every step kernel-checked in default mode.
3. **Layer 3** — induction synthesis (predicate from `peelUniversal` body, base via layer-2 emitter on `P(ZERO)`, step via `case on` IH + shift table, `schema_instance` citing `induction`); RED = `tests/cases/cooper_parity.bpa` and the `examples/peano.bpa` `evenOrOdd` flip. Named deferred boundaries: nested/multi-∃ alternation and period-D>cap (both DECLINE, never emit unsound).
