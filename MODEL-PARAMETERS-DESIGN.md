# Design: models, subgroups, and theorems parameterized on models

This doc records a design conversation (2026-08-03) that started from an awkward
subgroup-intersection model block and worked toward "theorems parameterized on
models." The endpoint (parameterized theorems) is the second half; this first half
captures the ARCHITECTURAL reasoning and the alternatives explored/rejected/deferred
along the way, so the *why* isn't lost.

---

# Part I — the architecture we worked through

## Starting pain: the awkward intersection model block

To prove "Z2 ∩ Z3 is a subgroup" today, the caller writes one giant model block
(see `z2z3-intersection.bpa`): it maps BOTH abstract subgroup predicates
(`inSubgroup`, `inSubgroup2`) onto the two concrete ones AND discharges six criteria
AND re-plumbs the whole group signature onto itself. Three stacked pains:
1. **identity re-plumbing** — `subgroup.Grp: Grp`, `subgroup.op: op`, … map symbols
   to themselves (noise);
2. **the `inSubgroup2` clone** — `std/subgroup.bpa` models a "second subgroup" as a
   hand-duplicated predicate + axioms, so the intersection is stated against two
   cloned copies the caller must both map;
3. **per-predicate criteria** — each predicate drags its three criteria mappings.

## The central mental model: a `model` is a MAPPER, inert until REIFIED

The crux the user landed on: **a `model` is just a theorem/axiom mapper** — a
correspondence (this sort/symbol/axiom ↦ that one) that DOES NOTHING until the
`model` command REIFIES it (materializes the remapped source proofs into
kernel-checked synthetic theorems in your file). Before reification: a
correspondence. After: actual proven theorems. A model is NOT a first-class value in
the FOL, NOT an object that persists and carries state; it is a reification event.
Every later idea is understood through this lens: "binding the parent," "composing
subgroups," "taking models" are all questions about *what reification produces* and
*whether one reification can consume another's output*, not about models-as-values.

## Idea: a subgroup is a model that BINDS ITS PARENT group

Wanted: a subgroup expressed as a model bound to its ambient group —
`model HsgG = Subgroup { parent: G, ... }`, with `H` the subgroup and `parent: G`
naming the group it lives in. Two subgroups of the same `G` share `parent: G`, which
is what lets an intersection combinator recognize "same parent." Resolved detail:
**`parent:` binds just the CARRIER SORT** — so the "parent slot" is just a sort
mapping (`subgroup.parent: G` ≈ today's `subgroup.Grp: Grp`), essentially free, no
new machinery.

## Rejected (infeasible): `sort H = G where inH` — a true SUBSET SORT

The cleanest surface would be `sort H = G where inH(G)` — `H` IS `G` restricted to
the `inH` elements, a real sort usable anywhere. VERDICT: **infeasible without adding
SUBTYPING to the kernel.** A `SortId` is an atomic tag; the kernel knows only sort
*equality*. A subset sort needs `H <: G` subsumption, coercion at application,
auto-injection of `inH(h)` at binders and auto-discharge at instantiation — i.e. a
different type system. That atomicity is deliberate (it underwrites `tautology` /
finite-model soundness). The guarded model ALREADY provides the same expressive
power: `∀h: H; P` and `∀g: G; inH(g) -> P` are the SAME proposition — the guarded
model writes the relativization explicitly instead of hiding it in the sort. So the
realistic version of `sort H` is at most SUGAR desugaring to the guarded form (a
guarded binder `∀x: G, inH(x); …` → `∀x: G; inH(x) -> …`), never a real sort. User:
"maybe it's fine" — acceptable, possibly dressed up later.

## The duplication trap, and its resolution

Making `H` its own group (own sort/ops/axioms) would force RE-PROVING the group
corpus on `H` (`cancelRightH`, `invInvolutionH`, all 10) inside `subgroup.bpa` —
exactly what `model` exists to avoid. Resolution: a parent-binding is only sensible
COMBINED with `model` — `H`'s group-ness comes from MODELING `H` onto `group.bpa`
(transport the corpus, no re-proof), not from restating theorems. Binding names the
parent; the model kills the duplication.

## The two-layer TRANSPARENT stack (preferred), vs. the opaque one-layer form

Two ways to get "H is a group":
- **One-layer (REJECTED — opaque):** a single subgroup model that, when you cite a
  *group* theorem through it, SILENTLY pulls in the criteria to discharge closure.
  Fewer keystrokes, but the discharge steps are HIDDEN — you can't walk the
  dependency chain from the citation. User rejected this precisely for the hidden
  steps (violates the walkability the dump test / `query uses` / taint model rely on).
- **Two-layer (PREFERRED — transparent):**
  ```
  model HSubGroup = G where inH { subgroup.parent: G, subgroup.op: ... }   // reifies the criteria
  model HGroup    = G where inH { group.opAssoc: <HSubGroup discharge>, ... } // reifies group-ness
  theorem hIdentityUnique: ...  [by model(HGroup) group.identityUnique]       // transfer, relativized to inH
  ```
  Every discharge is a NAMED, walkable mapping: "how is H a group? → HGroup →
  discharges closure via HSubGroup → proves criteria via these axioms." Fully
  transparent. This transparency is a hard USER REQUIREMENT (see the Transparency
  section in Part II) — prefer explicit named instances over any implicit
  auto-discharge, everywhere.
  Note: the group LAWS (assoc/identity/inverse) hold on all of G, so their
  relativized obligations AUTO-WEAKEN for free (already implemented, incl. the
  multi-binder `opAssoc`); `HGroup` genuinely needs `HSubGroup` only for the CLOSURE
  obligations (`inH(E)`, `inH(op(a,b))`, `inH(inverse(a))`) = the three criteria.

## Iterated subgroups K < H < G (OPEN — two readings, not reconciled)

`model KSubGroup = ... where inK ... { parent: <H?> }` exposed a fork:
- **Flatten to G** — K is a subset of the BASE group guarded by `inH and inK` (a
  conjunction guard). Composes trivially on existing machinery, but LOSES the
  hierarchy (K only exists as a subset of G, not "as a subgroup of H").
- **True nesting** — K's parent is H itself. This is the real math, but needs "H" to
  be a thing the `parent` slot can point at — a first-class model/guarded-sort, not a
  bare sort. This is the `sort H` problem again.
  DEFERRED. (This is why the user reached for `sort H`: with a real subset sort,
  K < H < G is just `parent: H`, `parent: G` — clean nesting. Because H isn't a sort,
  the hierarchy must be flattened-onto-G or encoded via a model-valued parent.)

---

# Part II — theorems parameterized on models

## The want

A theorem should take **models as parameters**, prove a result generically over
them, and be *applied* to concrete models at the use site — so a result like
"the intersection of two subgroups is a subgroup" is proved ONCE, generic over any
two subgroup-models, instead of being baked against cloned predicates
(`inSubgroup`/`inSubgroup2`) that every caller must re-map.

Target surface (syntax negotiable):

```
// in std/subgroup.bpa — proved once, generic over two subgroup-models:
theorem intersectionHasIdentity(M1, M2): M1.filter(E) and M2.filter(E)
proof
  @identity-in-first  | M1.filter(E)  [by model(M1) subgroup.hasIdentity]
  @identity-in-second | M2.filter(E)  [by model(M2) subgroup.hasIdentity]
  @conclusion | M1.filter(E) and M2.filter(E)  [by and_intro identity-in-first identity-in-second]
qed

// at the use site — apply it to two concrete subgroup models:
model HKGroup = G where inH and inK {
  opAssoc: subgroup.intersectionAssoc(HSubGroup, KSubGroup)
  ...
}
```

## The key realization: this is SCHEMA THEOREMS with a model argument kind

bpa already has **schema theorems** — theorems parameterized by term / formula /
predicate-lambda arguments, checked PER-INSTANTIATION with kernel re-check. The
machinery (elaborate.zig):

- `SchemaArg = union { value: Typed, lambda: {body, arg_sort, result_sort} }`
  (line 187) — the two kinds of argument a schema param can be bound to.
- `schema_args: ?*const SchemaArgs` (line 136) — the param→arg binding active while
  a schema body is elaborated.
- `instantiateSchemaCore` (line 1542) — binds `schema_args`, re-elaborates the body,
  and (when `recheck_schemas`) **re-runs `checkProofSteps` at THIS instance**. This
  is exactly the user's chosen semantics: **per-application, kernel-re-checked.**
  Caching = memoize on (schema, args) — a later optimization, deferred.
- `instantiating: []StatementId` (line 141) — the cycle guard, already handles
  self/mutual instantiation.

So "theorems parameterized on models" = **schema theorems whose parameters may be
bound to models** — a new `SchemaArg.model: ModelId` variant. Per-application
semantics, re-check, cycle-guard: ALL inherited from the schema mechanism. No
functor system, no abstract proof-checking, no kernel change.

## The careful part: a model arg is consumed at TWO layers (not one)

A `value`/`lambda` schema arg is consumed in exactly ONE place — `elaborateExpr`
(a term/formula position): `.value` substitutes a term (line 3085), `.lambda`
beta-reduces at application (line 3117). A **model** argument is different — it
appears where a term never does, at two distinct touch-points:

1. **Projection — `M1.filter`, `M1.subgroup.hasIdentity`** (symbol-resolution
   layer). `M1.filter` in the STATEMENT/body resolves to the model's mapped
   predicate (`inH`), so `M1.filter(E)` elaborates to `inH(E)`. This threads into
   `elaborateSymRef` / `elaborateCall` (lines 3093, 3109): when a qualified head's
   base is a bound model param, resolve `.<component>` through that model's maps
   (`sort_map` / `sym_map` / `stmt_map` in the Model struct).

2. **Citation — `[by model(M1) subgroup.hasIdentity]`** (justification layer). Here
   `M1` is consumed by the `model` accelerant (`justify` in accelerant/model.zig,
   line 38), NOT by `elaborateExpr`. Today `model(<Instance>)` looks the instance
   up in `self.models` by name (line 48). It must ALSO accept an instance that is a
   bound schema param → the concrete model it's bound to.

Both are LOOKUPS into a Model's existing maps — the maps exist; the work is
routing the param name to them at these two sites. Naming both is the crux of
getting this right: it is NOT "a third variant consumed like the other two."

## Pieces, in dependency order

**P0. `model(M) thm` as a mapping/citation VALUE (prerequisite, independently
useful).** Today a model-mapping RHS and a `[by …]` value must be a plain
identifier; `group.opAssoc: model(HSubGroup) subgroup.opAssoc` does NOT parse. Allow
a `model(X) thm` citation as a mapping value (parser + desugar: materialize it into
a synthetic named theorem via the existing `materializeModelTheorem`, then point the
mapping at that theorem's id). This is the "transparent two-layer stack"
(`HSubGroup` → `HGroup`) AND the substrate for applying a parameterized theorem.
Small; reuses the materializer. **Spike this FIRST** — it also proves nested-model
materialization (one model's obligation discharged by transferring through another)
composes and kernel-checks.

**P1. Model parameters on a theorem — `theorem foo(M1, M2): …`.** At DEFINITION
time, record it as a schema-like template with model params; nothing is checked
(schemas already defer checking to instantiation, line 441). Store the param names.

**P2. Projection `M.component`.** In `elaborateSymRef`/`elaborateCall`, when a
qualified head's base is a bound model param, resolve `.component` through that
model's maps. Small — lookup.

**P3. `model(M)` citation with M a bound param.** In accelerant/model.zig `justify`,
resolve the instance token: if it's a bound schema-model-param, use the concrete
model it's bound to. Small — one branch at line 48.

**P4. Application `foo(HSubGroup, KSubGroup)`.** The instantiation: bind the model
params (new `SchemaArg.model`), run `instantiateSchemaCore` — which re-elaborates
the body (P2/P3 now resolve) and re-checks at the kernel. The ENGINE is the existing
schema instantiation; the new part is the `model` arg kind + the two resolution
sites. Medium.

**P5 (caching, DEFERRED).** Memoize instances on (template, model-args) so a repeated
`foo(HSubGroup, KSubGroup)` materializes once. Pure optimization; user parked it.

## Orthogonal prerequisite: conjunction guards

The intersection TARGET `model HKGroup = G where inH and inK` needs a guard that is
a CONJUNCTION, not a single predicate. Today `Remap.Guard = { pred: SymId, carrier }`
(term.zig:314) — a single predicate symbol. Options: (a) require a defined
`pred inHK(g) := inH(g) and inK(g)` and guard on that symbol (no guard-machinery
change; a `define`); (b) generalize `Guard.pred` to a guard FORMULA with one hole.
(a) is far cheaper and probably sufficient. Independent of P0–P4; needed only for the
intersection target, not for the parameterized theorem itself.

## Transparency (a user requirement)

The user explicitly rejected the one-layer "subgroup model silently transfers group
theorems by auto-pulling the criteria" path BECAUSE its discharge steps are hidden
and un-walkable. Every design choice here must keep the dependency chain explicit
and citable: `HKGroup` discharges via a NAMED `intersectionAssoc(M1,M2)` instance,
which cites `model(M1) …` / `model(M2) …`, which materialize checkable theorems.
`query uses` / the dump test must be able to walk it. Prefer explicit named
instances over any implicit auto-discharge.

## Syntax: the "does it MOVE?" principle

The load-bearing distinction (user): **`[by theorem X]` / `[by axiom X]` are BARE
citations — no kernel move.** The kernel's `axiom_ref`/`theorem_ref` just
`requireClaim(step, X.formula)` — the step must α-match the cited fact exactly; no
derivation (kernel.zig:327). By contrast **`model(M) X` is NOT a bare citation — it
is a MOVE**: resolve M, remap X's statement through the interpretation, materialize
the remapped proof, cite that. The step's formula is X-relativized-through-M, not X.
So `model(...)` belongs with the byline *operations* (forall_elim, rewrite,
arithmetic(...), simplify), precisely because work happens. This gives a uniform rule:

- **`model(...)` = a MOVE** (unwrap / transfer / materialize) → byline. STAYS
  `[by model(M) X]` (user-settled). Do NOT collapse to `@`.
- **`M@component` = NO move** (inert projection / name resolution) → term/statement
  position. `M@filter` resolves to the mapped predicate (`M@filter(E)` = `inH(E)`);
  it is like `.` namespace-dotting, does nothing. Being in expression position, `@`
  does not collide with the `@label` step-sigil (label position only; lexer
  disambiguates on the preceding token — an `@` after an identifier is the infix
  projector).

### A parameterized theorem is a LEXICAL UNROLL, and its body cites are BARE

Crucial correction (user). Inside a parameterized theorem, a citation of a model
component is NOT a `model(M)` move — it is a BARE citation of a PROJECTED NAME:

```
// statement + body: projection everywhere; cites are bare `[by axiom ...]`
theorem intersectionHasIdentity(M1, M2): M1@subgroup.filter(E) and M2@subgroup.filter(E)
proof
  @identity-in-first  | M1@subgroup.filter(E)   [by axiom M1@subgroup.hasIdentity]
  @identity-in-second | M2@subgroup.filter(E)   [by axiom M2@subgroup.hasIdentity]
  @conclusion | M1@subgroup.filter(E) and M2@subgroup.filter(E)
    [by and_intro identity-in-first identity-in-second]
qed
```

At APPLICATION `intersectionHasIdentity(HSubGroup, KSubGroup)`, the schema unroll
substitutes `M1 -> HSubGroup`, `M2 -> KSubGroup`; `M1@subgroup.hasIdentity` PROJECTS
through HSubGroup's maps to the concrete fact it bound (e.g. `z2HasIdentity`, whose
statement is `inZ2(E)`); `M1@subgroup.filter(E)` projects to `inZ2(E)`. The claim
and the projected axiom's statement then MATCH, so the bare `[by axiom z2HasIdentity]`
kernel-checks. Pure unroll — no per-cite move.

Why this is sound HERE and not always: the moves already happened at the MODEL
DECLARATIONS (`model HSubGroup = ... { subgroup.hasIdentity: z2HasIdentity }`). The
parameterized theorem doesn't transfer anything; it NAMES facts its supplied models
already carry. This works because the intersection theorem is UNGUARDED (a statement
over the base group about two predicates) — so projecting a component yields the
mapped fact's statement VERBATIM, matching the claim. IF a parameterized theorem
were guarded (projection relativizes the statement), a bare projection cite would NOT
match and a `model(M)` move would be needed. Intersection is the clean unguarded case.

Consequence for the design: the two model-consumption layers are
(1) **projection `M@component`** — used in BOTH the statement AND the body cites
    (`[by axiom M@thm]`), a pure name resolution through the model's maps, no move;
(2) **`model(M) X` move** — used to TRANSFER a foreign theorem onto a new
    interpretation (the declaration/reification sites), not inside a parameterized
    theorem's bare cites.
This is simpler than "two layers, one of which is a move at every cite": inside a
parameterized theorem, EVERYTHING is projection + bare citation.

### Disposition on the open notation choices (user)

SETTLED NOW (verified, not awaiting the spike):
- `model(M) X` is a MOVE; `[by axiom/theorem X]` is a BARE cite. This is what the
  kernel already does (`axiom_ref` = `requireClaim`, no derivation) — iron today.
- For the UNGUARDED intersection theorem, the body cites unroll to BARE. Verified
  against `z2z3-intersection.bpa`: the projected fact's statement (`inZ2(E)`)
  α-matches the claim verbatim, no relativization. Not a guess.

STILL OPEN (discovered by implementation, NOT chosen by taste):
- the mapping-value RHS notation (below);
- whether a GUARDED parameterized theorem's body cites stay bare or need a move
  (inferred, not yet verified — the guard would relativize the projected statement).
Whichever is correct is forced by soundness — a bare projection cite that doesn't
α-match its projected fact is simply wrong, not a style option. Requirements on the
resolution of the STILL-OPEN items:
- **Consistent** — one rule, applied everywhere the situation arises.
- **Iron / no user knob** — the user CANNOT pick; exactly one is sound and the tool
  enforces it. Do not expose a flag or a "both accepted" leniency.
- **Deferred** — we cannot know which until we implement P0 and see how nested
  materialization actually composes. Do not fix the notation before the spike.

### OPEN (decide during P0): the mapping-value RHS

A model MAPPING value that discharges an obligation by transferring through another
model — `group.opAssoc: ???` — is UNDETERMINED between:
- `model(HSubGroup) subgroup.opAssoc` — if the transfer/materialization happens
  HERE (a move, consistent with the byline); vs.
- `HSubGroup@subgroup.opAssoc` — if the RHS merely NAMES which theorem discharges
  the obligation and the actual materialization is deferred to the OUTER model's
  pass (a projection).
Which one is correct depends on how P0 structures nested materialization — is the
inner transfer eager (here) or folded into the outer model's materialization? Decide
after the P0 spike; do not fix the notation before then.

## What this is NOT

- NOT ML functors with abstract signature checking. Per-application (chosen), so no
  proving-against-an-abstract-model. The source theory (`subgroup`) already IS the
  interface; a concrete model supplies the structure; instantiation is
  substitute-and-recheck.
- NOT a kernel change. Everything rides on the existing schema-instantiation
  re-check and the model materializer.
- NOT models-as-first-class-values in the FOL. A model is still a mapper; it is
  reified at the `model`/instantiation command. Parameterization = a schema arg kind.

## Suggested sequencing

1. **Spike P0** (hand-written named-workaround first, then the `model(M) thm` value)
   — proves nested-model materialization composes. Gate it. This alone unlocks the
   transparent two-layer subgroup-is-a-group stack.
2. **P1–P4** — the `SchemaArg.model` extension + the two resolution sites +
   application. Fixture: `intersectionHasIdentity(M1,M2)` proved once, applied to two
   concrete subgroup models.
3. **Conjunction guard** (option a) — enables the `HKGroup = where inH and inK`
   target; wire the parameterized intersection theorems into it.
4. **P5 caching** — when/if instance counts warrant it.
```
