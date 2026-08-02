# MODEL-DESIGN.md — the `model` mechanism (structure reuse / "X is-a Y")

Branch `isa-structure-reuse`. This supersedes the syntax/mechanism portion of
`ISA-EXPLORATION.md` (which recorded the *terrain*; this records the *decision*).
Status: **syntax + trust model SETTLED; not yet fully done — see "Still open".**

## What it is

A `model` declaration says a target sort **is a** model of an imported abstract
theory, by giving a mapping from the theory's primitives+axioms to local symbols
+facts. Once declared, the theory's entire derived-theorem corpus is available at
the target, remapped, cited through the model. This is the model-theoretic "Int
is a model of the group axioms" — hence the keyword `model`.

Motivating cases: **ℚ under `+` is a group** (guard-free) and **ℚ∖{0} under `×`
is a group** (guarded by `nonzero`) — two models of the *same* theory on the
*same* sort, which is what forces named instances. (ℤ additive-group +
multiplicative-*monoid* was the earlier driver; ℚ is sharper because both are
groups, exercising the two-models-of-one-theory collision.) The original
forcing function remains **nonneg-ℤ is-a Peano ℕ** (guarded), to retire the
hand-duplicated ℕ-algebra-over-ℤ in `std/integer-ring.bpa`.

## Design philosophy — `model` is comptime structural transfer (the Zig way)

This is the framing that makes `model` bpa's distinctive contribution, and it is
a **design constraint**, not just a description. Every open question is decided by
whether the answer keeps `model` comptime-shaped.

The *capability* — prove theorems over an abstract theory, transfer them to a
concrete structure by discharging axioms — is exactly what **Lean typeclasses**,
**Isabelle locales**, and **Rocq module functors / structures** already do. bpa is
NOT claiming to do something they cannot. The distinctiveness is in the SHAPE:

> **`model` is to typeclasses/locales what Zig `comptime` is to C++ templates +
> concepts.** Same expressive target; opposite implementation values.

- **Explicit over implicit — no resolution engine.** Lean *searches* for the
  instance; `model` is NAMED at the cite site (`[by model AdditiveGroup with
  group.cancelLeft]`). Zig has no trait search; you pass/name the thing. The named
  cite IS the Zig answer to instance resolution: refuse action-at-a-distance.
- **Structural over nominal.** `Rat` does not *declare conformance* to `Grp`; you
  assert a mapping and the checker verifies the shape (obligations discharge),
  failing at the use site if not — `comptime` duck-typing lifted to proofs. No
  subtype hierarchy, no `instance` declaration the theory has to know about.
- **Monomorphize-and-forget over carry-the-dictionary.** `remapFormula` is
  comptime codegen: it emits the concrete theorem's AST from the abstract one and
  is DONE. No dictionary passing, no vtable, no residual machinery at
  proof-checking time. The big provers carry the typeclass dictionary; bpa
  specializes the formula once and moves on.
- **Tiny kernel, power beside it.** `model` is a disclosed, tainted, kernel-EXTERNAL
  rewrite (an accelerant, see Trust model). The kernel never learns what a
  "structure" is — same architectural bet as Zig's small-language + comptime, and
  as bpa's small-kernel + accelerants. It came out this shape because it inherits
  Zig's values, not despite being written in Zig.
- **LLM-authorable.** A model block is a flat mapping table a language model can
  write and read; typeclass instance resolution is implicit action-at-a-distance
  that is hard to author without a feedback loop. Legibility is bpa's whole reason
  to exist, and the comptime shape is what keeps `model` legible.

### The invariant (the non-goal that defines the feature)

**Stay comptime-shaped: explicit at the cite, structural not nominal, resolved-to-
concrete-and-done, no dictionary, no search.** Test any proposed extension by:
*would this be a comptime transform, or would it need a runtime/resolution
mechanism?* If the latter, it is not bpa's `model` anymore — it is a worse
reimplementation of the thing the big provers already do well.

Concretely, these would BREAK the distinctiveness and are therefore NON-GOALS:
- **Automatic model discovery** ("find the model that makes this goal go through").
  The cite must always name the instance.
- **Transitive model chains resolved by search** (`group models monoid`,
  `Rat models group`, ∴ `Rat` gets monoid theorems automatically). If chaining is
  ever wanted, it must be an explicit, spelled-out composition — not search.
- **Coherence machinery** — two search paths to the same theorem needing to be
  reconciled. There are no search paths; there is one named cite.

## Syntax

### Declaration

```
model <carrier> [where <guardPred>] as <InstanceName> {
  <source.primitive>: <localSymbol>    // sort + op maps
  ...
  <source.axiom>:     <localFact>      // axiom OBLIGATIONS, discharged by naming
  ...                                  //   a local fact of the (remapped) shape
}
```

- **`source: target` direction** (`group.Grp: Rat`, `group.op: add`). Left is the
  *source* entity, right is the local thing it maps to. This mirrors how
  `remapFormula` reads the table (walk source formula, look up each symbol → its
  target) AND makes the completeness check trivial: enumerate the source theory's
  primitives+axioms, verify every one appears as a key exactly once. A missing
  key is a clear error ("model `AdditiveGroup` doesn't map `group.opInverseLeft`").
- **Uniform lines.** Every line is `source: local`. Primitives map symbols; axiom
  lines map an obligation to a local FACT (not a proof block) — you *name* a local
  axiom/theorem whose formula already has the remapped shape. No
  `theorem … proof … qed` inside the block.
- **`as <InstanceName>`** — mandatory. Two models of one theory coexist on one
  sort (`AdditiveGroup`, `MultiplicativeGroup`), disambiguated by name.
- **`where <guardPred>`** — optional carrier relativization. `Rat where nonzero`
  means the carrier is the `nonzero` subdomain; every source `Grp`-binder picks up
  a `nonzero(bound) ->` antecedent (see Relativization).

Example (guard-free):
```
model Rat as AdditiveGroup {
  group.Grp:      Rat
  group.E:        ZERO
  group.op:       add
  group.inverse:  neg
  group.opAssoc:  addIsAssociative   // + the other 4 axiom obligations
}
```

Guarded:
```
model Rat where nonzero as MultiplicativeGroup {
  group.Grp:      Rat
  group.E:        ONE
  group.op:       mul
  group.inverse:  inv
  group.opAssoc:  <a local Rat fact, already guarded by nonzero>
}
```

### Citation (using a transferred theorem)

```
theorem addCancelLeft: forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
proof
  @conclusion |
    forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
    [by model <InstanceName> with <source.theorem>]
qed
```

`model` is a **built-in justification-verb** (like `axiom`, `rewrite`) — NOT a
user-defined tactic (bpa has none). `[by model AdditiveGroup with group.cancelLeft]`
remaps `group.cancelLeft`'s formula through the `AdditiveGroup` mapping and checks
it equals the step goal. The cite names BOTH the instance (which mapping) and the
source theorem (what to transfer) — necessary because a sort has multiple models.
(Cite spelling: `[by model <InstanceName> with <source.thm>]`; the redundant
`<carrier> as` before the instance name is dropped since the name resolves the
carrier. TBD if we keep the short form.)

## The engine: `remapFormula`

The one genuinely new piece. `formula: TermId` PERSISTS on every checked `Fact`
(env.zig:44-70) — the statement AST survives after proof-checking (only the proof
is consumed). So every source theorem is a live `TermId` to walk; no re-parse, no
re-elaborate.

`remapFormula(formula: TermId, mapping, guard: ?pred) -> TermId`: a structural
walk over `term.zig`'s Node union emitting a new tree into the arena with

- **`SortId` substituted** (Grp→Rat) — including the `sort` field inside `fvar`
  and `quant` nodes, not just top-level;
- **`SymId` substituted** (op→add, E→ZERO, inverse→neg) in `app`/`pred` nodes;
- **guard injection** (guarded case): each `quant` over the mapped carrier sort
  gets its body wrapped `guard(bound) -> body`.

This is ONE pass, run in BOTH directions:
- **IN** (obligation check): remap each source axiom, check it equals the named
  local fact's formula. `remapFormula(group.opAssoc, m) == addIsAssociative.formula`.
- **OUT** (theorem transfer): remap the cited source theorem, check it equals the
  cite goal.

Closest existing precedent is `instantiateSchema`'s symbol substitution, but that
substitutes term/predicate PARAMS, not sorts+arbitrary-syms across a whole
formula. No such helper exists yet — this is the build.

Note: `group`'s primitives are all opaque `func`/`const` (no `define`), so the
`definition: ?TermId` transparency path doesn't arise for this theory. Guard
against mapping onto a `define`d symbol later.

## Trust model — `model` is an ACCELERANT

Classified with `assoc`/`arithmetic`/Cooper-replay. (Vocabulary per
`accelerated-elaborated-vocab`: kernel-checked vs. accelerated/disclosed; flag is
`--fast` vs. default. There is NO `--pure`.)

- `[by model … with …]` **taints** the citing theorem — `accelerated` gains
  `"model"` — **disclosed in the summary**.
- **`--fast`**: trust the transfer wholesale — take the remapped formula, skip the
  obligation-discharge check and the source proof. (MVP path.)
- **default**: **elaborated** — the transfer is legitimate (not tainted) because
  (a) every source axiom obligation is checked to be discharged by a real local
  fact (remap-and-match), and (b) the source theorem was already proven over the
  abstract sort. Both hold ⇒ transferred theorem is sound.

Subtlety vs. other accelerants: `model`'s soundness is **compositional**
(faithful-interpretation + source-proof-valid), not a decision procedure. That is
an internal detail of *how* it elaborates, not new vocabulary or a new flag.

## Relativization (the guarded case)

A guarded model (`where nonzero`) makes `remapFormula` inject `guardPred(bound) ->`
at every quantifier over the mapped carrier — applied UNIFORMLY in both directions:

- **OUT**: `group.cancelLeft`'s `forall a,x,y: Grp; op(a,x)=op(a,y) -> x=y` →
  `forall a,x,y: Rat; nonzero(a) -> nonzero(x) -> nonzero(y) -> mul(a,x)=mul(a,y) -> x=y`.
- **IN**: the author's discharging fact must ALREADY carry the `nonzero` guards
  (decision (A): the guard lives in the local fact, not synthesized/stripped by the
  checker). The `where nonzero` on the head is what tells `remapFormula` to inject;
  the same pass keeps IN and OUT symmetric.

## MVP staging (accelerant pattern, as with Cooper-replay/assoc)

1. **`--fast` transfer first** — parse `model` block, build the id→id mapping,
   `remapFormula` the cited source theorem (unguarded case), check it matches the
   goal, taint. This alone proves the whole mechanism (sort-map + theorem-remap).
   Test: `Rat`/`Int` gets `cancelLeft`/`inverseUnique`/etc. under `--fast`.
2. **default-mode obligation discharge** — check every `group.*` axiom is mapped to
   a local fact whose remap matches; then transferred theorems are un-tainted.
3. **guarded models** — relativization pass; `where nonzero`; ℚ∖{0} mult-group and
   nonneg-ℤ-is-a-ℕ.

## Still open (not yet decided)

- Cite short form: keep `[by model <Instance> with <thm>]` or allow/require the
  full `<carrier> as <Instance>`?
- Do transferred theorems ALSO materialize as citable namespaced facts
  (`AdditiveGroup.cancelLeft`) at declaration time, or ONLY reachable via the
  `[by model … with …]` cite? (Namespace-shadowing was raised then set aside; the
  cite-verb form is what's settled. Materializing would let other tactics see them.)
- Completeness policy: MUST every source axiom be mapped (total), or may a model be
  partial (map a sub-signature)? Total is the clean default.
- `where <guard>` for guards that aren't a single unary pred (e.g. a conjunction).
- Multi-sort source theories (a theory with two carrier sorts) — mapping scales,
  but not exercised by group/monoid.
```
