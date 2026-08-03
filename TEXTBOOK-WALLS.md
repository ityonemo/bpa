# Textbook walls — sketches for the two blocking gaps

Building the AATA Chapter 1 transliterations (`aata/1.2.*.md`), the proofs stayed
mechanical *within the expressible fragment* — the 13 set identities all fell out
of one `extensionality → fix x → unfold → tautology` template, composition-assoc
was a short rewrite chain. The pain was never the logic or the tactics; it was the
**ontology**: what can be an object. Two gaps wall off most of the interesting
exercises, and they recur across every chapter. Sketches below.

The through-line: `std/set.bpa` models a set as a **flat `member(x, S)` predicate
over one fixed `Element` universe**. Clean, but a set cannot contain a set, a
function cannot be a set of pairs, and no object can be built by choice. Each gap
is a real design fork, not a papercut.

---

## Gap 1 — collections (sets of sets) : the recurring wall

Blocks, across chapters:
- equivalence relations ⟺ partitions (`1.2.3-partitions.md` is mostly `hole`s:
  `classesCoverUniverse`, `classesDisjoint`, … only check under `--draft`);
- indexed families `⋃ᵢ Aᵢ` / arbitrary unions & intersections over a collection
  (`1.2.1-sets.md:113`);
- anything quantifying over "a collection of sets".

### The tension

The flat model deliberately has ONE membership relation `member(Element, Set)`.
A partition is a `Set` *of* `Set`s with `member(Set, Collection)` — a SECOND
membership at a different type. bpa's FOL is many-sorted, so a second predicate
at a second sort is legal; the question is how much reuse we keep.

### Sketch A — a `Collection` sort layered ON TOP (minimal, recommended first step)

A new std theory `std/collection.bpa`, importing `std/set.bpa`, that treats a
collection as opaque with its own membership `contains(Collection, Set)` — exactly
the shape `std/set.bpa` already has, one level up:

```
import set <<< "std/set.bpa"
sort Set = set.Set
sort Collection
pred contains(c: Collection, s: Set)              // Set ∈ Collection

// union over a collection: x ∈ ⋃C  iff  ∃ s; contains(C, s) ∧ member(x, s)
func bigUnion(c: Collection): Set
axiom bigUnionMember: forall c: Collection; forall x: Element;
  (member(x, bigUnion(c)) -> (exists s: Set; contains(c, s) and member(x, s)))
  and ((exists s: Set; contains(c, s) and member(x, s)) -> member(x, bigUnion(c)))

// analogous bigIntersection with a `forall s` body.
// collection extensionality: same members ⇒ equal (mirrors set extensionality).
```

**What this unlocks immediately:** indexed-family unions/intersections, and the
`bigUnion(classes) = Universe` / pairwise-disjoint statements a partition needs
(`contains(C, s) ∧ contains(C, t) ∧ s ≠ t → intersection(s,t) = emptyset`). The
partition ⟺ equivalence theorem becomes stateable — the classes of `~` form a
`Collection`, and the two directions are membership arguments in the SAME
`tautology`/extensionality style that already works.

**Cost:** ~1 new file (~15 declarations), no kernel change. The `bigUnion`
membership carries an `exists`, so the pointwise proofs use `exists_intro`/
`exists_elim` rather than pure `tautology` — heavier than the flat identities but
the same shape as the order-theory exists proofs already in `std/peano-ordering`.

**Limit:** it does NOT give a general cumulative hierarchy — `Collection` and
`Set` are distinct sorts, so you can't nest arbitrarily (a collection of
collections needs a third sort). That's fine for Chapter 1 (partitions are one
level up) and keeps the model first-order and decidable-friendly. Going deeper
(true set-of-sets, `∈` uniform at every level) is Sketch B.

### Sketch B — a uniform membership hierarchy (deeper, deferred)

One sort `V` (sets-in-the-von-Neumann-sense) with a single `elem(V, V)` and an
extensionality axiom, so everything is a set of sets of … . This is what real
set-theoretic math wants, but it's a big commitment: `elem` at one sort loses the
type discipline that makes the flat model's `tautology` proofs finite (atoms stop
being obviously distinct), and unrestricted comprehension is a soundness minefield
(Russell). If we go here it must be a *typed/bounded* fragment (separation only,
no comprehension), and it wants its own design pass. **Recommendation: ship
Sketch A, revisit B only if a later chapter genuinely needs nesting.**

---

## Gap 2 — choice / definite description : the "construct the witness" wall

Blocks:
- the BACKWARD half of invertible ⟺ bijective (`1.2.2-functions.md:1000`) — the
  forward half is fully constructive and ships;
- generally, anything that builds a function/object from a "for each x a unique y"
  spec.

### The tension

`std/function.bpa` models `Fn` as an opaque sort with `apply(f, x)`. To prove
"injective ∧ surjective ⇒ invertible" you must *exhibit* an inverse `g` and
discharge `invertibleDef`'s `exists g`. Surjectivity gives `∀y ∃x; apply(f,x)=y`;
injectivity makes that `x` unique. But bpa's FOL has no operator turning
`∀y ∃!x; P(x,y)` into a NAMED function `g` with `apply(g,y) = x` — no ε/ι, no
choice. So the witness for `exists g` cannot be constructed.

### Sketch — a definite-description constant, guarded by uniqueness

Add, in `std/function.bpa` (or a `std/choice.bpa` it imports), a
description-forming operator that is SOUND because it fires only under a proven
uniqueness hypothesis:

```
// `theFn(spec)` names the function determined by a pointwise relational spec,
// PROVIDED the spec is total-and-unique. `spec: Element -> Element -> Prop` is
// the "apply(g, y) should be x" relation.
func theFn(spec: Element -> Element -> Prop): Fn                 // needs a Prop-valued fn param (schema-style)
axiom theFnApply:
  forall spec;
    (forall y: Element; exists x: Element;                       // total
       spec(y, x) and (forall x2: Element; spec(y, x2) -> x = x2))  // + unique
    -> (forall y: Element; spec(y, apply(theFn(spec), y)))       // theFn realizes it
```

Read: *if* `spec` picks exactly one `x` per `y`, *then* `theFn(spec)` is a function
that, applied to `y`, gives that `x`. The uniqueness antecedent is what keeps it
from being global choice (no well-ordering, no AC over arbitrary sets — this is
definite description, the tame ι, not the ε). The bijection-backward proof then:
builds `spec(y, x) := apply(f, x) = y`; proves total (surjectivity) + unique
(injectivity); instantiates `theFnApply`; the resulting `theFn(spec)` is the
inverse, discharging `exists g`.

**Cost:** the axiom needs a `Prop`-valued function parameter — that's the schema
machinery (`axiom foo(spec: Element -> Element -> Prop): …`), which bpa already
has (`std/fol.bpa` schemas over `Prop`). So likely NO kernel change; it's an
axiom-schema in `std/function.bpa` plus the backward proof. Verify the schema
param can be a binary `Prop`-relation (today's schemas are unary `Nat -> Prop`
shaped — may need a small elaborator extension for the two-arg relational param).

**Soundness note:** this is a genuine axiom addition (definite description is not
derivable in bare FOL). It's conservative over the uniqueness-guarded fragment —
worth a one-paragraph justification in the file header and disclosure that any
theorem using it rests on `theFnApply` (the `hole`/accelerated-style provenance
already tracks axiom dependence). It is strictly weaker than choice: it cannot
pick from a non-unique set, only realize a proven-unique spec.

---

## Priority

**Gap 1 / Sketch A is the highest-leverage single unlock** — it's the prerequisite
for partitions, indexed families, AND (via a product/pair sort, a small further
step) the relational view of functions. Gap 2 is narrower (the bijection
biconditional and similar constructions) and cheaper (probably schema-only, no new
sort). Neither needs a kernel change in its recommended (A / description) form;
both are new std theories + literate proofs, the same shape as the work already
landed. The deep versions (B, full choice) are real design forks — defer until a
chapter forces them.

---

## The payoff plan — functions as sets of pairs, modeled as abstract `Fn`

Once Gap 2 (definite description) lands, the textbook-faithful move is: a function
IS a set of pairs, and that CONCRETE construction is a `model` OF the abstract
opaque `Fn` theory — so the whole `Fn` corpus (composition-associativity,
invertible⇒bijective, …) transfers onto the pair representation for free. Same
shape as group→ring→ℤ, applied to functions. Direction matters: the pair-set is
the carrier; `Fn` is what it's a model of; the abstract corpus flows DOWN onto the
concrete objects.

Build order (each layer additive, no kernel change beyond what Gap 2 needs):
1. **`std/pair.bpa`** — a `Pair` sort, `pair(a, b)`, `fst`/`snd`, projection axioms.
2. **Sets of pairs** — alias `set.Element = pair.Pair`; `std/set.bpa` then gives
   `member(Pair, Set)` for free (the shared-`Element` design paying off exactly as
   intended).
3. **`std/function-pairs.bpa`** — the carrier: `isFunction(S)` (single-valued
   guard), `applyPair(S, a)` = the unique `b` with `pair(a, b) ∈ S` (**this is an
   ι-term — Gap 2 is load-bearing here**), `composePair`, `identityPair`. Prove
   each `Fn` axiom as a LOCAL theorem over pair-sets — notably `funcExtensionality`
   flips from axiom to *theorem*, discharged by set extensionality.
4. **The model** — `model FunctionAsPairs = Set where isFunction { function.Fn:
   Set, function.apply: applyPair, … }`. Guarded (`where isFunction`): the
   relativization threads `isFunction(bound) ->` through every carrier binder, so
   transferred theorems come back relativized, and you discharge the guards at each
   cite (needs lemmas like `isFunction(f) ∧ isFunction(g) → isFunction(compose)`).

### Risk assessment (honest)

- **The `model` stratum is REVERSIBLE.** The pair theory + the `model` block + the
  transferred cites are an additive layer over untouched foundations. If the
  guard-discharge burden gets ugly or a transfer won't go through, delete the
  `model` block — the pair-set theory still stands on its own, and nothing
  downstream of the opaque `Fn` theory breaks (it is never modified). So concerns
  about guard relativization at scale and "is the transfer worth it" are
  *find-out-by-trying*, not *de-risk-first*: build it, roll back if it doesn't earn
  its keep.

- **The ONE thing to spike first is Gap 2's definite description**, because it is
  NOT in the reversible layer — it sits UNDERNEATH the whole construction
  (`applyPair` can't be named without it). And the element-extraction form
  (`theElement(pred)` = the unique `x` with `pred(x)`) is subtly different from the
  `theFn` sketch above; verify a `Prop`-valued/relational schema parameter is
  stateable with TODAY's schema machinery (unary `Nat -> Prop` is the current
  shape). If it is (likely) → the whole stack is low-risk, proceed. If it needs a
  kernel/elaborator change → know THAT before investing in pairs/function-pairs/
  model, since it's the load-bearing, non-reversible foundation.

Net: architecturally sound and worth doing; the model layer needs no up-front
proof (roll back if it fails), but do a ~30-minute spike on definite-description-
of-an-element as a schema before building on it.
