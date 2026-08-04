# Design: models, subgroups, and theorems parameterized on models

This doc covers the `model` mechanism for structure reuse and its extension to
theorems parameterized on models. The motivating problem is proving "the intersection
of two subgroups is a (sub)group" once, generic over any two subgroups. The first
half captures the architectural reasoning — the alternatives explored, rejected, and
deferred — so the *why* isn't lost; the second half specifies the
parameterized-theorem mechanism.

---

# The architecture

The design evolved through several readings of the same idea (not competing
options), each surfacing the insight that motivated the next.

## Background: a `model` is a MAPPER, inert until REIFIED

The crux underlying all of this: **a `model` is just a theorem/axiom mapper** —
a correspondence (this sort/symbol/axiom ↦ that one) that DOES NOTHING until the
`model` command REIFIES it (materializes the remapped source proofs into
kernel-checked synthetic theorems in your file). Before reification: a
correspondence. After: proven theorems. A model is NOT a first-class value in the
FOL; it is a reification event. "Binding the parent," "composing subgroups," "taking
models" are all questions about *what reification produces* and *whether one
reification can consume another's output*.

Also settled along the way:
- **Guarded binders** `forall x: G, inH(x); P` are sugar for `forall x: G; inH(x) -> P`.
- A true SUBSET SORT `sort H = G where inH` is **infeasible** — it needs kernel
  subtyping (SortIds are atomic; the kernel knows only sort equality). That
  atomicity underwrites `tautology`/finite-model soundness. The guarded model is the
  substrate; `sort H` is at most sugar over it, never a real sort.
- **`parent:` binds just the carrier sort** — so the parent slot is essentially a
  sort mapping, ~free.

## The two-layer stack: transferring the group corpus onto a subgroup

Two stacked models. `HSubGroup` reifies the subgroup criteria; `HGroup` reifies
group-ness, DISCHARGING its closure obligations by transferring THROUGH `HSubGroup`
via a `model(...)` value in the mapping. Then a group theorem transfers through
`HGroup`, relativized to `inH`. Preferred BECAUSE every discharge is a named,
walkable mapping — no hidden steps (the user rejected the opaque one-layer
alternative for exactly this: it would silently pull in the criteria, un-walkable).

```
sort G;
import group <<< ...
// whatever axioms/theorems G needs to be a group
pred inH;

model HSubGroup = G where inH {
  subgroup.parent: G
  subgroup.op: ...
}

model HGroup = G where inH {
  group.opAssoc: model(HSubGroup) subgroup.opAssoc   // <-- discharge THROUGH another model
}

// K < H < G  (the iterated-subgroup wrinkle — OPEN, see below)
model KSubGroup = G where inH where inK? {
  subgroup.parent: G where inH?
  subgroup.op: ...
}

// asserting H is a group, one property at a time (here identityUnique):
theorem hIdentityUnique: forall x: Grp, inH(x); (forall g: Grp, inH(g); op(x, g) = g) -> x = E
proof
  @one-step |
    forall x: Grp, inH(x); (forall g: Grp, inH(g); op(x, g) = g) -> x = E
    [by model(HGroup) group.identityUnique]
qed
```

The key new capability this needs: **`model(HSubGroup) subgroup.opAssoc` as a
MAPPING VALUE** — a model obligation discharged by a citation through another model.
This does NOT parse today (a mapping RHS must be a plain identifier); it is the
prerequisite for everything (see the pieces list) and proves nested-model
materialization composes.

This transfer is preferred BECAUSE every discharge is a named, walkable mapping — no
hidden steps (the opaque one-layer alternative was rejected for exactly this: it
would silently pull in the criteria, un-walkable).

The `?`-marked lines (`KSubGroup = ... where inH where inK?`, `parent: G where inH?`)
are the ITERATED-SUBGROUP wrinkle K < H < G, left OPEN: two readings —
- **flatten to G**: K guarded by `inH and inK`, a conjunction over the base group;
  composes on existing machinery but loses the hierarchy;
- **true nesting**: K's parent is H itself — needs "H" to be a thing the `parent`
  slot can point at (a first-class model/guarded-sort). This is the `sort H` problem.
Not reconciled.

## Theorems parameterized on models (the intersection generalization)

The two-layer stack discharges obligations for ONE subgroup. Intersection needs a result proved
GENERICALLY over TWO subgroups. So a theorem takes MODELS as parameters, its
statement/body PROJECT through them (`Model1.subgroup.filter`, `model(Model1) ...`),
and the use site APPLIES it to concrete models. This removes the `inSubgroup2` clone
entirely — the "second subgroup" is just a second model parameter.

```
sort G;
import group <<< ...
pred inH
model HSubGroup = G where inH {
  subgroup.parent: G
  subgroup.op: ...
  subgroup.filter: ...
}

// note: K NOT (necessarily) < H — two independent subgroups of the same G
pred inK
model KSubGroup = G where inK {
  subgroup.parent
  subgroup.op
  subgroup.filter: ...
}

// in std/subgroup.bpa — proved ONCE, generic over two subgroup-models:
theorem intersectionHasIdentity(Model1, Model2): Model1.subgroup.filter(E) and Model2.subgroup.filter(E) {
    @identity-in-first |
      pred1(E)
      [by model(Model1) subgroup.hasIdentity]
    @identity-in-second |
      pred2(E)
      [by model(Model2) subgroup.hasIdentity]
}
theorem intersectionAssoc(Model1, Model2): ...

// usage — the intersection target is a CONJUNCTION-guarded model whose obligations
// are discharged by APPLYING the parameterized theorems to the two models:
model HKGroup = G where inH and inK {
  opAssoc: subgroup.intersectionAssoc(Model1, Model2)
  opIdentityLeft: subgroup.identityLeft(Model1, Model2)
}
```

New capabilities this needs (beyond the mapping-value prerequisite): model PARAMETERS on a theorem,
`Model.component` PROJECTION, model APPLICATION `thm(M1, M2)`, and the CONJUNCTION
GUARD `where inH and inK` for the intersection target. Mechanism analysis in the
second half of this doc.

## Iterated subgroups (K < H < G)

The genuine subgroup-of-a-subgroup hierarchy, flagged by the `?`s in the two-layer
stack — RESOLVED via flatten. The
two readings were flatten-to-G vs. true-nesting. **SETTLED: flatten.** K's
membership `inK` is a SINGLE predicate over the base group `Grp`, `K = Grp where
inK` a single-guard sort, and `inK(g) -> inH(g)` records K ⊆ H. This keeps every
guard single-predicate, so the guarded-transfer engine works UNCHANGED — the
iterated hierarchy composes on existing machinery. (True nesting would need the
guarded-materialization engine — assume/discharge/weaken in accelerant/model.zig —
generalized from one guard predicate to a LIST, a bounded but real change; deferred
in favor of the flatten.) True nesting — K's parent genuinely H — is deferred to a
future "model spaces" rebuild (a first-class-interpretation reworking), because the
single-guard→list generalization fights the carrier-lowering rather than removing it.

The ONE mechanism gap it surfaced (now fixed): transferring a DIRECTLY-MAPPED AXIOM.
`[by model(HGroup) group.opAssoc]` and the `@`-projection value
`group.opAssoc: HSubGroup@subgroup.opAssoc` both cite `group.opAssoc`, which is an
AXIOM (no proof to materialize). The materializer now consults the model's
`stmt_map` FIRST (in `justify` and at the top of `materializeModelTheorem`) and
cites the mapped discharge directly — exactly as `remapCitation` already did for a
fact reached transitively inside a proof. Fixture: `tests/cases/model_subgroup_transfer.bpa`
(BOTH levels — the 8-theorem group corpus onto H, then three theorems onto the
sub-subgroup K — kernel-checked, untainted).

---

# The parameterized-theorem mechanism

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

1. **`model(M) thm` as a mapping/citation VALUE (prerequisite, independently
useful).** Today a model-mapping RHS and a `[by …]` value must be a plain
identifier; `group.opAssoc: model(HSubGroup) subgroup.opAssoc` does NOT parse. Allow
a `model(X) thm` citation as a mapping value (parser + desugar: materialize it into
a synthetic named theorem via the existing `materializeModelTheorem`, then point the
mapping at that theorem's id). This is the transparent two-layer stack
(`HSubGroup` → `HGroup`) AND the substrate for applying a parameterized theorem.
Small; reuses the materializer. **Prototype this first** — it also proves nested-model
materialization (one model's obligation discharged by transferring through another)
composes and kernel-checks.

2. **Model parameters on a theorem — `theorem foo(M1, M2): …`.** At DEFINITION
time, record it as a schema-like template with model params; nothing is checked
(schemas already defer checking to instantiation, line 441). Store the param names.

3. **Projection `M.component`.** In `elaborateSymRef`/`elaborateCall`, when a
qualified head's base is a bound model param, resolve `.component` through that
model's maps. Small — lookup.

4. **`model(M)` citation with M a bound param.** In accelerant/model.zig `justify`,
resolve the instance token: if it's a bound schema-model-param, use the concrete
model it's bound to. Small — one branch at line 48.

5. **Application `foo(HSubGroup, KSubGroup)`.** The instantiation: bind the model
params (new `SchemaArg.model`), run `instantiateSchemaCore` — which re-elaborates
the body (projection and citation now resolve) and re-checks at the kernel. The ENGINE is the existing
schema instantiation; the new part is the `model` arg kind + the two resolution
sites. Medium.

6. **Caching (DEFERRED).** Memoize instances on (template, model-args) so a repeated
`foo(HSubGroup, KSubGroup)` materializes once. Pure optimization; parked.

## Orthogonal prerequisite: conjunction guards

The intersection TARGET `model HKGroup = G where inH and inK` needs a guard that is
a CONJUNCTION, not a single predicate. Today `Remap.Guard = { pred: SymId, carrier }`
(term.zig:314) — a single predicate symbol. Options: (a) require a defined
`pred inHK(g) := inH(g) and inK(g)` and guard on that symbol (no guard-machinery
change; a `define`); (b) generalize `Guard.pred` to a guard FORMULA with one hole.
(a) is far cheaper and probably sufficient. Independent of the pieces above; needed only for the
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

SETTLED NOW (verified, not awaiting the prototype):
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
- **Deferred** — we cannot know which until we implement the mapping-value
  prerequisite and see how nested materialization actually composes. Do not fix the
  notation before that prototype.

### OPEN (decide during the mapping-value prototype): the mapping-value RHS

A model MAPPING value that discharges an obligation by transferring through another
model — `group.opAssoc: ???` — is UNDETERMINED between:
- `model(HSubGroup) subgroup.opAssoc` — if the transfer/materialization happens
  HERE (a move, consistent with the byline); vs.
- `HSubGroup@subgroup.opAssoc` — if the RHS merely NAMES which theorem discharges
  the obligation and the actual materialization is deferred to the OUTER model's
  pass (a projection).
Which one is correct depends on how the mapping-value prerequisite structures nested
materialization — is the inner transfer eager (here) or folded into the outer model's
materialization? Decide after that prototype; do not fix the notation before then.

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

1. **Prototype the mapping-value prerequisite** (hand-written named-workaround first,
   then the `model(M) thm` value) — proves nested-model materialization composes.
   Gate it. This alone unlocks the transparent two-layer subgroup-is-a-group stack.
2. **The parameterized-theorem pieces** — the `SchemaArg.model` extension + the two
   resolution sites + application. Fixture: `intersectionHasIdentity(M1,M2)` proved
   once, applied to two concrete subgroup models.
3. **Conjunction guard** (option a) — enables the `HKGroup = where inH and inK`
   target; wire the parameterized intersection theorems into it.
4. **Caching** — when/if instance counts warrant it.
```
