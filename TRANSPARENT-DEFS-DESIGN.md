# Transparent predicate definitions — design notes

Status: **DESIGN / MULLING.** No implementation. This captures the problem, the
empirical survey of the codebase, the central tension (which the survey exposed),
and the compromise fault-line to decide before building. Deferred behind the iff
work (which is the manual precursor — see "Relationship to iff", below).

## The goal

Kill the fold/unfold *step* tax on defined predicates. Today an opaque
`pred prime(p)` carries its meaning in *separate axioms*; every use that needs the
meaning must cite the axiom, `forall_elim` it, and unpack — ~3 kernel steps *per
use*, and the intermediate formulas are all materialized and re-checked. In a
definition-heavy proof (FTA is the worst) this dominates. A transparent def makes
`prime(p)` and its meaning *definitionally interchangeable*, so the unfold is free
(zero steps) rather than a cited axiom dance.

Parallels the existing `define` for term-functions (transparent term expansion);
this extends transparency to **predicates**.

## Two big prior decisions (settled earlier)

- **Lazy, not eager.** `foo` survives as a *named atom* in kernel terms carrying
  its definition as associated data; it unfolds on demand — NOT expanded away at
  parse time. Reason: **remodeling**. If `foo` were eagerly inlined before the
  `model` machinery runs, a model could never remap `foo` as a symbol (the name is
  gone). Lazy keeps `foo` a first-class symbol a model can map, while still folding
  for readable formulas/errors. (The cost of lazy is the deep part: the kernel gains
  a notion of definitional equality — see "The kernel defeq mechanism".)
- **Model orthogonality is NOT free** (revised). Originally we thought transparent
  preds would simply never appear in `model{}` blocks. The remodeling motivation
  overturns that: a model MAY remap a transparent pred's name, and soundness then
  requires a **definition-agreement check** — see "Models and remodeling".

## The empirical survey (what the codebase actually contains)

Every opaque `pred` in std/ was classified by HOW its axioms characterize it. Three
shapes emerged (full inventory below). This is the finding that makes the feature
non-trivial: **not all defined predicates have a closed-form body.**

### Shape A — single biconditional (closed-form). ~14 preds. UNFOLDABLE.
Characterized by exactly one `foo(args) iff <body>` — written today either as a
literal `iff` (post the iff-sweep) or as an intro/elim axiom PAIR (the two halves of
one biconditional). Each collapses to `pred foo(args) := <body>`.

| pred | body |
|---|---|
| `divides(d,n)` (Dividable / Nat / Int — 3 copies) | `exists k; n = mul(d, k)` |
| `less_than(a,b)` (Nat / Int) | `exists d; [nonneg(d) and] add(a, succ(d)) = b` |
| `less_or_equal(a,b)` (Nat / Int) | `exists d; [nonneg(d) and] add(a, d) = b` |
| `reflexive` | `forall x; related(x, x)` |
| `symmetric` | `forall x, y; related(x, y) -> related(y, x)` |
| `transitive` | `forall x, y, z; related(x,y) -> related(y,z) -> related(x,z)` |
| `equivalence` | `reflexive and symmetric and transitive` |
| `injective(f)` | `forall a, b; apply(f,a) = apply(f,b) -> a = b` |
| `surjective(f)` | `forall y; exists x; apply(f, x) = y` |
| `invertible(f)` | `exists g; compose(g,f) = identityFn and compose(f,g) = identityFn` |
| `covers(c)` | `bigUnion(c) = universe` |
| `pairwiseDisjoint(c)` | `forall s, t; contains(s,c) -> contains(t,c) -> s != t -> intersection(s,t) = emptyset` |
| `isPartition(c)` | `covers(c) and pairwiseDisjoint(c) and (forall s; contains(s,c) -> s != emptyset)` |
| `inSeqBelow(x,s,k)` | `exists i; is_nonneg(i) and below(i,k) and at(s,i) = x` |

### Shape B — structural / per-constructor. 2 preds. NOT closed-form.
`member(x, s)` (set) and `contains(s, c)` (collection). Characterized by ONE axiom
per CONSTRUCTOR of the recursed argument:
```
member(x, union(a,b))        iff  member(x,a) or member(x,b)
member(x, intersection(a,b)) iff  member(x,a) and member(x,b)
member(x, difference(a,b))   iff  member(x,a) and not member(x,b)
member(x, complement(a))     iff  not member(x,a)
not member(x, emptyset)
```
There is **no single body** for `member(x, s)` with arbitrary `s`. `member(x, ATOM)`
(atomic/variable set) is PRIMITIVE — irreducible. The definition is *distributed
across cases keyed on the argument's head symbol*. This is "Shape A with
pattern-matching": each clause is a conditional biconditional guarded by a
constructor pattern.

### Shape C — inductive / relational-parameter. 5 preds. NOT unfold at all.
`related`, `nonneg`, `inSubgroup`, `inSubgroup2`, `oneStepSubset`.
- `related(x,y)` — a FREE binary relation, deliberately opaque, constrained only
  indirectly (via reflexive/symmetric/transitive when assumed). A theory *parameter*.
- `nonneg(n)` — the LEAST set containing ZERO and closed under succ; carries an
  explicit `nonnegInduction` schema witnessing leastness.
- `inSubgroup`/`inSubgroup2`/`oneStepSubset` — subgroup membership: closure axioms
  (has identity, closed under op/inverse) defining a least/constrained subset.

You CANNOT rewrite `nonneg(n)` into a formula — membership is established by
*derivation* (intro rules) and reasoned about by *induction*, not decided by a body.
This is a genuinely different mechanism from unfold.

## The central tension (this is the thing to decide)

Every opaque pred IS a definition; they differ in the SHAPE of the definition, and
each shape wants a different unfold story:

| shape | "definition" is | unfold behavior |
|---|---|---|
| A closed-form | one body | total: `foo(t)` -> body[t] always |
| B structural | one rule per constructor | partial: fires only when the argument's head matches a clause; else stays folded |
| C inductive | least set closed under rules | none: never rewrites; use intro rules forward + an induction principle |

**A and B can plausibly share ONE mechanism** — "guarded unfold": a transparent def
is a list of clauses `pattern => body`, unfold picks the clause whose pattern matches
the argument (A = the degenerate single clause with a variable pattern; B = several
constructor-keyed clauses; no match => stays folded as an opaque residue).

**C cannot join them.** An inductive predicate is not unfoldable; its proper feature
is an `inductive` definition form that GENERATES the intro rules + the induction
schema (a generated schema, not a rewrite). Forcing C into the transparent-def
mechanism is what would make the design incoherent — keep it separate.

### The remodeling axis cuts across, and it's reassuring
Shape C preds (`related`, `inH`, `inSubgroup`) are EXACTLY the abstract-theory
PARAMETERS a `model` fills in. They *want* to stay opaque, remappable symbols. So "C
is not a transparent def" is not a loss — those preds should remain model-mappable
symbols, as today. The preds worth making transparent (A, maybe B) are the *derived*
notions layered on top of the parameters, not the parameters themselves.

## The compromise fault-line — WHERE DOES B LAND?

This is the open decision. C is settled (separate future `inductive` feature). The
fork is whether B (member/contains) unifies with A or defers with C:

- **NARROW — transparent = A only (closed-form `:=`).** B and C both deferred to the
  future inductive/structural feature. Simplest, contained, covers the FTA
  definition-unfold pain. BUT `member` — the pred that motivated "we need to handle
  that case" — stays exactly as painful as today.
- **MIDDLE — transparent = A + B (guarded-clause unfold, matches on argument head).**
  One unfold mechanism (clauses; A = 1 trivial clause). Covers member/contains. C
  stays the separate inductive feature. Moderately more complex (pattern-matched
  unfold, "no clause matched -> folded residue" semantics), and it DOES address the
  case raised.
- **WIDE — one mechanism for A+B+C.** Believed to be a mistake: C isn't unfold. Listed
  for completeness.

Recommendation leaning MIDDLE if `member` ergonomics are a real target, NARROW if the
first cut should just unblock FTA and defer everything structural. USER IS MULLING.

## The kernel defeq mechanism (needed once scope is set)

Lazy transparent defs require the kernel to relate `foo(t)` and its unfolding. Two
options (decide with scope):
- **Explicit `unfold`/`fold` proof rule (contained).** `foo` stays a distinct atom;
  a new kernel-checked rule rewrites `foo(t) <-> body[t]` (like `rewrite`). `alphaEq`
  stays syntactic — you cite `unfold` where you need the body. Small trusted-core
  change; cheaper than today's axiom dance but not invisible.
- **Kernel definitional equality (deep).** `alphaEq`/matching treat `foo(t) ≡ body[t]`
  transparently everywhere; unfolding is automatic and never cited (max prover-work
  win, fully invisible), formulas fold for display but compare as-if-unfolded. Every
  term-keyed cache / alphaEq / remap becomes defeq-aware — a real extension to the
  trusted kernel.

The MIDDLE scope (guarded clauses) interacts here: with pattern-matched unfold, "the
body" depends on the argument, so a naive `foo(t) ≡ body` defeq needs the match to be
decidable at compare time. The explicit-`unfold`-rule option sidesteps that (you cite
which clause), which is a point in its favor if B is in scope.

## Models and remodeling — RESOLVED (ride-along-only) + partly LANDED

The full-corpus audit (every model block × every define-candidate pred) settled
this: **ride-along-only suffices; NO candidate needs a nominal-mapping mechanism.**
- All 14 Shape-A candidates are clean single-biconditionals → all become `define`.
- The ONLY model-involved candidates are `divides` (nominal `divisibility.divides:
  divides`, RIDE-ALONG-SAFE: abstract body `∃k;n=mul(d,k)` under Dividable→Int,mul→mul
  is α-equal to the ℤ body — the nominal line dissolves) and `invertible` (the guard
  pred on `InvFn`, closure logic works on the unfolded body — ride-along-safe). Every
  other candidate lives in a theory that is not a model source → not model-involved.
- Reconciles the earlier "orthogonality vs lazy-for-remodeling" tension: BOTH were
  right. A transparent pred is never a model mapping LINE (orthogonality), AND
  remodeling still happens — via unfold-then-ride-along on the body's primitives,
  which REQUIRES lazy (the body must be reachable to unfold at remap time). Lazy
  serves ride-along, not nominal mapping.

**The rule:** transparent (`define`d) preds ride along on their body's primitives;
they are never a model mapping source. Migration: delete `divisibility.divides:
divides` (+ the vanished dividesIntro/dividesElim mappings); `divides` follows `mul`.

**LANDED (commit "model + define: reject transparent SOURCE, expand transparent
TARGET"):** the define/model interaction is already implemented and gated, ahead of
the pred-shaped `define` surface, using today's nullary term-`define` as the
transparent symbol:
- **SOURCE guardrail** — a `define`d symbol as a model mapping source is REJECTED
  (elaborate.zig map-builder, keyed on `Symbol.definition != null`). RED fixture
  `model_define_source_bad.bpa` (previously silently accepted).
- **TARGET expansion** — a `define`d symbol as a mapping TARGET is allowed and now
  WORKS: the source symbol expands to the target's body during transfer (new
  `Remap.expands` side-table SymId→body, consulted in `remapApp`; defaults empty so
  existing models are untouched). RED→GREEN fixture `model_define_target.bpa`.
- Caveat for the pred-shaped rollout: current defines are NULLARY, so `remapApp`
  expansion does no arg-substitution. Parameterized `define`d preds (`divides(d,n)`)
  will need the body's param-fvars substituted by the (remapped) actual args at the
  expansion site — the one extension the pred case adds here.

### Original derivation (kept for context)

Grounded in the ONE real precedent — `IntegerDivisibility` maps
`divisibility.divides: divides` PLUS `dividesIntro`/`dividesElim` (the two axioms).
With `divides` transparent on both sides, the two axioms VANISH (definitionally
true); the model maps only the `divides` symbol, and soundness requires:

> **Definition-agreement check:** a model may remap `foo -> bar` (foo transparent) iff
> `remap(body_of_foo) ≡ body_of_bar` under the model's other mappings (α-equality).
> For `divides->divides`: `remap(∃k; n=mul(d,k)) = ∃k; n=mul(d,k) = target body` ✓.

This single check REPLACES the old "map the intro + elim axioms" — one defeq check
instead of two axiom mappings. Only Shape A (single body) needs it; if B is in scope,
the check generalizes to clause-wise agreement.

Survey confirmed: across 27 model blocks, only 2 remap a predicate
(`set.member->contains`, `divisibility.divides->divides`), BOTH opaque->opaque today,
NO definitional content currently mapped. So this is greenfield — no legacy to break.
`member->contains` is Shape B (stays opaque unless B is in scope); `divides->divides`
is the Shape A migration poster child.

## Relationship to iff (already shipped)

`iff` + `iff_rewrite` (landed on integer-number-theory) are the MANUAL precursor:
- The Shape A preds were the ones the iff-sweep rewrote from intro/elim pairs (or
  inline conjunctions) into single `foo(args) iff body` axioms. That `iff` axiom IS
  the closed-form body — so the transparent-def migration for Shape A is mechanical:
  `axiom fooDef: foo(args) iff body`  ->  `pred foo(args) := body`.
- `iff_rewrite` is the manual unfold: given `fooDef`, rewrite `foo(t)` <-> `body[t]`
  in a goal. Transparent defs make this automatic (and free). So iff_rewrite stays
  useful for THEOREM-level equivalences (`invertible iff bijective` — not a
  definition) while transparent defs subsume the DEFINITIONAL iffs.
- The `iff`-shaped axioms in the corpus are therefore a ready-made migration list for
  the Shape A rollout.

## Migration surface (once built, Shape A)

Convert each Shape A pred `pred foo(args)` + `axiom fooDef: foo(args) iff body` into
`pred foo(args) := body`; delete `fooDef`; every `iff_rewrite fooDef` /
elim-then-reason site becomes automatic unfold. Update `IntegerDivisibility` model to
the definition-agreement form. Gate counts shift (axioms disappear, proofs shorten).

## Open questions to resolve before coding
1. **Where does B land** — MIDDLE (guarded clauses, unify with A) vs NARROW (defer with
   C)? [central; user mulling]
2. **defeq mechanism** — explicit `unfold` rule (contained) vs kernel definitional
   equality (deep/invisible)? Interacts with (1): B pushes toward explicit unfold.
3. **Recursion** — may a transparent body mention another transparent pred? Almost
   certainly yes but ACYCLIC (ban self/mutual recursion; that's the `inductive`
   feature's job). Needs a cycle check at declaration.
4. **Printing** — fold for display in errors / `query outline` (show `prime(p)`, not
   the 60-char body) even though the kernel may compare unfolded. Load-bearing for
   readability; the whole point of lazy.
5. **`inductive` feature (Shape C)** — scope as its OWN design doc later; generates
   intro rules + induction schema. `nonneg`/`inSubgroup`/`member`(if B defers here).
