# bpa language guide

This guide covers the whole surface: every keyword, the proof rules, how
the kernel establishes trust, and the built-in automation. For naming and
style conventions see `CONVENTIONS.md`; for the accelerated-tactic registry see
`ACCELERATION.md`.

## Files and checking

A `.bpa` file is a sequence of declarations. `bpa check file.bpa` verifies
them in order; every failure is reported as `file:line:col: error:
<message>` on stderr, and success prints one summary line:

```
OK: 18 declarations, 6 theorems proven (1 accelerated: arithmetic)
```

By default `bpa check` **verifies everything**: `by arithmetic`/`by
tautology` must produce a checkable certificate (an accelerated fallback is a hard
error), imported proofs are re-checked, and imported schemas are
re-instantiated. Speed flags defer that work during development, one layer
each, and say so loudly in the summary:
- `--fast` — accept accelerated verdicts for arithmetic/tautology
- `--faster` — also trust imported theorem proofs (skip re-check)
- `--reckless` — also trust imported schemas (skip re-instantiation)
- `--draft` — allow `hole`s (aspirational placeholders); orthogonal to the
  above. Default mode rejects any file with holes and lists them.

Re-run plain `bpa check` to fully verify before finalizing. `bpa fmt`
normalizes whitespace and indentation (`--check` reports instead of
rewriting).

## Declaration keywords

### `sort`

Declares a sort (a domain of discourse). `Prop`, the sort of propositions,
is currently the only built-in. Sorts are typically capitalized; the
following declares "Natural Numbers":

```bpa
sort Nat
```

### `const`

Declares an uninterpreted constant of a sort.

```bpa
const ZERO: Nat
```

### `define`

Names a term.  Expansion is performed transparently at elaboration — the
kernel only ever sees the underlying term, so definitions add nothing to
the trusted surface and work everywhere a term does, including inside automation.
Definitions may build on each other. The sort is inferred.

```bpa
define TWO = succ(succ(ZERO))
define FOUR = succ(succ(TWO))
```

### `func`

Declares a function symbol with argument and result sorts. An optional
`requires` clause guards the function: every application incurs a proof
obligation that the guard holds, discharged against facts available at the
use site (an undischarged obligation is an error).

```bpa
func succ(n: Nat): Nat
func div(a: Nat, b: Nat): Nat requires b != ZERO
```

### `pred`

Declares a predicate (a function into `Prop`). Zero-argument predicates
are atomic propositions and may be written bare.

```bpa
pred less_than(a: Nat, b: Nat)
pred raining
```

### `axiom`

Asserts a formula without proof. Axioms are the file's assumptions;
`grep 'by axiom'` audits exactly where they are used.

```bpa
axiom addZeroLeft: forall b: Nat; add(ZERO, b) = b
```

### `theorem`

Asserts a formula with a `proof ... qed` block, which the kernel checks.

```bpa
theorem addZeroRight: forall n: Nat; add(n, ZERO) = n
proof
  ...
qed
```

### `hole`

An **aspirational placeholder** — a claim stated up front, accepted mechanically
like an `axiom`, but tracked as a hole. Use it to **scaffold** (state a lemma,
build the proof that needs it, fill it in later) or to **reason conditionally**
("suppose an odd perfect number exists; here is what follows"). Cited exactly
like an axiom: `[by axiom myHole]`.

```bpa
hole zeroIsEven: even(ZERO)
```

Holes are **disclosed, never silent**: a theorem that (transitively) rests on a
hole is tracked, and **default mode REJECTS the file** — it exits nonzero and
lists each hole with its `file:line` and the theorems that depend on it, so a
hole-bearing result is never mistaken for complete. `--draft` allows holes
(exit 0) with a loud banner naming them. Holes are **orthogonal** to the speed
flags: `--fast` never accepts a hole; only `--draft` does. Once you prove a
hole, turn it into a `theorem`.

### Schematic axioms and theorems

A parenthesized parameter list makes an `axiom` or `theorem` **schematic**:
a stored form with `comptime` semantics. It is not checked at declaration;
each `instantiate` use substitutes concrete, written-out arguments and (for
theorem schemas) re-checks the proof at that instance. Formula-valued
parameters are supplied as `fun` lambdas.

```bpa
axiom induction(prop: Nat -> Prop):
  prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)

theorem contrapositive(p: Prop, q: Prop): (p -> q) -> (not q) -> (not p)
proof
  ...
qed
```

Instantiations are **not cached**: a plain theorem is checked once and cited
by reference thereafter, but a schema's proof is re-run at every instantiation
site (the parameters differ, so there is no single fixed result to cache). If
an expensive instance is reused, **realize it into a named theorem** — write a
plain `theorem` whose one step is `[by instantiate NAME(args) ...]`, and cite
that theorem from then on. Naming pays the instantiation cost once and reuses
it through the ordinary `proven`-flag mechanism; it also keeps the reuse
explicit and greppable rather than hidden in a kernel memo table.

(This is guidance for today, not a guarantee. We may cache instantiations
directly in the future — but a proof checker whose *soundness surface* has to
care about assistant speed is a design smell, so any such cache would have to
earn its keep without expanding what must be trusted. For now, caching stays
in the language, as named theorems.)

### `forward`

Promises that a name will be defined later in this file as a theorem — a
verified table of contents. A missing or wrongly-kinded definition is an
error at the `forward` line.

```bpa
forward addIsCommutative
```

### `import`

Loads another file under a namespace. Members are referenced with
qualified names (`peano.Nat`, `peano.addZeroLeft`). Paths beginning
`std/` resolve in the standard library (`$BPA_STD_DIR`, default `./std`);
other paths resolve relative to the importing file.

```bpa
import peano <<< "std/peano.bpa"
```

By default imported theorems are re-checked. Under `--faster`/`--reckless`
they are trusted (proofs not re-checked) and counted separately in the
summary. Schematic theorems are re-checked at each instantiation (in the
instantiating file) by default, and trusted only under `--reckless`.

### Aliases

Any declaration keyword followed by `= qualified.name` creates a
kind-checked **view** of an imported entity — a local name for the same
thing, not a copy, so facts proved through either spelling interoperate.

```bpa
sort Nat = peano.Nat
func add = peano.add
axiom addZeroLeft = peano.addZeroLeft
theorem addIsCommutative = peano.addIsCommutative
```

### `model` *(forthcoming — design settled, not yet implemented)*

Declares that a local sort **is a model of** an imported abstract theory, so
that theory's whole proven corpus transfers to the local sort. Where an alias
identifies one entity with another, a `model` identifies a *whole structure* —
you map each of the theory's primitives (its carrier sort, operations,
constants) and discharge each of its axioms, and in exchange every theorem the
theory proves becomes citable at your sort.

```bpa
import group <<< "std/group.bpa"

model AdditiveGroup = Rat {
  group.Grp:      Rat               // carrier sort
  group.E:        ZERO              // primitives: source symbol : local symbol
  group.op:       add
  group.inverse:  neg
  group.opAssoc:  addIsAssociative  // axiom obligations: source axiom : local fact
  // ... one line per remaining group axiom
}
```

Read every line **`source : target`** — the abstract theory's entity on the
left, the local thing that plays it on the right. Primitive lines map symbols;
axiom lines discharge an obligation by naming a local axiom or theorem whose
formula, seen through the mapping, *is* that axiom.

A model **may leave some axioms unmapped** — at the prover's risk. In default
(strict) mode, citing a transferred theorem whose proof depends on an unmapped
axiom is **rejected**, naming the missing obligation. Under `--fast` the same cite
**passes** (the transfer is trusted without checking which axioms it needed) —
disclosed as accelerated, but a loaded gun: treat a `--fast` pass over a partial
model as provisional until it also passes strict mode.

The head reads like any bpa alias/definition — the name being declared is left of
`=`, what it's a model *over* is on the right (`model AdditiveGroup = Rat`). The
instance is **named** because one sort can model one theory more than one way — ℚ
is a group under `+` *and* (on ℚ∖{0}) under `×`. Each named model keeps its own
mapping; a use names which.

**Guarded carriers.** A model may relativize its carrier to a subdomain with
`where <unaryPred>` (on the carrier, right of `=`):

```bpa
model MultiplicativeGroup = Rat where nonzero {
  group.Grp:      Rat
  group.op:       mul
  group.E:        ONE
  group.inverse:  reciprocal
  // ... axiom obligations, each already guarded by `nonzero`
}
```

`where nonzero` means the carrier is the `nonzero` elements; every transferred
theorem picks up a `nonzero(...)` guard on each of its bound variables (a
`forall a: Grp; P(a)` becomes `forall a: Rat; nonzero(a) -> P(a)`), and the
local facts discharging the axioms must carry the same guards. The guard is a
**single unary predicate** over the carrier sort; for a compound condition,
`pred`-declare or `define` it first and name that.

**Using a transferred theorem** — cite it through the model with the `model`
justification rule (see *Justification rules* / *Automation*):

```bpa
theorem addCancelLeft: forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
proof
  @conclusion |
    forall a, x, y: Rat; add(a, x) = add(a, y) -> x = y
    [by model(AdditiveGroup) group.cancelLeft]
qed
```

`[by model(AdditiveGroup) group.cancelLeft]` takes `group`'s abstract
theorem, rewrites it through the `AdditiveGroup` mapping (relativizing by the
guard if any), and checks the result equals the goal. It is an **accelerant**:
under `--fast` the transfer is trusted wholesale and marks the theorem
accelerated (disclosed in the summary); in default mode it is legitimate because
the model's axiom obligations were themselves checked and the source theorem was
already proven over the abstract sort — so nothing is trusted that wasn't
derived.

> `model` is bpa's lightweight take on what typeclasses (Lean), locales
> (Isabelle), and module functors (Rocq) do — but explicit and search-free: you
> name the instance at every use, the mapping is one level deep, and the transfer
> is a checked source-to-source rewrite that never enters the kernel. No instance
> resolution, no coherence machinery. (See `MODEL-DESIGN.md`.)

## Formulas

Quantifier binders end with a semicolon; connectives are words; `->` is
implication (right-associative), `and`, `or`, `not` are the other boolean
operators, and `=` / `!=` compare terms of the same sort.

**Mixed boolean operators require explicit parentheses.** A same-operator
chain is fine unparenthesized (`a or b or c`, `a -> b -> c`, `not not a`),
but nesting *different* boolean operators must be spelled out — `a and b or c`
is a parse error; write `(a and b) or c` or `a and (b or c)`. This applies to
all four operators, so `not p` as an operand of `and`/`or`/`->` also needs
parens (`(not p) and q`, `a -> (not b)`). The rule removes the classic
precedence-memory footgun: a formula reads one way to everyone, or it doesn't
parse. (`=` / `!=` are comparisons, not boolean operators, so they never need
parens against a connective: `x = y and p` is `(x = y) and p`.)

```bpa
forall a, b: Nat; add(a, b) = add(b, a)
exists w: Nat; add(x, succ(w)) = y
(not (p or q)) -> ((not p) and (not q))
```

`fun (k: Nat) => ...` lambdas appear only as schema arguments; they are
beta-reduced away during instantiation.

## Proofs

A proof is a sequence of steps. Each step is an `@`-sigiled label on its own
line, then — indented beneath it — the formula and its bracketed
justification:

```bpa
@have-imp |
  p -> q
  [by axiom pImpliesQ]
@conclusion |
  q
  [by modus_ponens have-imp have-p]
```

The `@` marks a step **definition**; it sits at the left margin so labels form
a scannable gutter column. Citations of a label are **bare** (no `@`) — the
sigil distinguishes a definition from a use. The final step of the proof must
state the theorem's formula. Labels are the reference currency: rules cite
earlier steps and enclosing blocks by (bare) label.

### Subproof keywords

**`assume`** opens a block under a hypothesis; discharging it with
`implies_intro` yields the implication, with `not_intro` the negation.

```bpa
@hyp |
  assume less_than(a, b) {
    ...
  }
@imp |
  less_than(a, b) -> less_than(a, succ(b))
  [by implies_intro hyp]
```

**`fix`** opens a block with a fresh, arbitrary variable; discharging it
with `forall_intro` yields the universal. Fix variables must be globally
fresh within the proof.

```bpa
@gen |
  fix n: Nat {
    ...
  }
@all |
  forall n: Nat; ...
  [by forall_intro gen]
```

**`unpack ... from`** opens a block naming the witness of a previously
established existential; `exists_elim` exports any witness-free conclusion.

```bpa
@use-witness |
  unpack u: Nat from witnessed {
    @hu |
      add(a, succ(u)) = b
      [by hypothesis use-witness]
    ...
  }
@exported |
  less_than(a, b)
  [by exists_elim use-witness]
```

**`case ... on`** states a goal, then proves it by splitting a previously
established disjunction into one arm per disjunct — sugar for a (possibly
nested) `or_elim`. Each arm is an `assume`-block over one disjunct that must
conclude the goal. A left-nested `(A or B) or C` fans out automatically; you
write N arms, not a hand-nested `or_elim` tree.

```bpa
@result |
  q1 = q2
  case on tri-q1q2 {
    @arm-lt |
      assume less_than(q1, q2) {
        ...
        @out |
          q1 = q2
          [by ...]
      }
    @arm-eq |
      assume q1 = q2 {
        @out |
          q1 = q2
          [by hypothesis arm-eq]
      }
    @arm-gt |
      assume less_than(q2, q1) {
        ...
        @out |
          q1 = q2
          [by ...]
      }
  }
```

The disjunction (`tri-q1q2`) is any prior step proving `A or B or ...`; the
"kind" of split is whatever lemma produced it (`trichotomy`, `zeroOrSucc`,
…). To split an existential, `unpack` its witness first, then
`case` on a disjunction about the now-in-scope witness. `case` is elaborator
sugar: the kernel checks the synthesized `or_elim` exactly as if hand-written,
so it adds no trust.

Steps may cite labels across the whole enclosing block regardless of textual
order (resolution is topologically sorted; a citation cycle is an error).
Nothing inside a closed subproof leaks out except through its discharge rule.

### Justification rules

`[by <rule> <refs>]`, where refs are step or block labels (and statement
names for citations). Rules taking a term argument write it in parens:
`[by forall_elim(succ(b)) some-step]`.

| Rule | Meaning |
|---|---|
| `axiom NAME` | cite an axiom verbatim |
| `theorem NAME` | cite a proven theorem verbatim |
| `hypothesis BLOCK` | restate an enclosing block's assumption (or unpacked witness fact) |
| `modus_ponens IMP ANT` | from `P -> Q` and `P`, conclude `Q` |
| `implies_intro BLOCK` | discharge an assume block as an implication |
| `forall_intro BLOCK` | discharge a fix block as a universal |
| `forall_elim(t, ...) STEP` | specialize a universal at one or more terms — `forall_elim(A, B)` peels two binders in one step (the intermediate chain is synthesized) |
| `exists_intro(t) STEP` | from `P[t]`, conclude `exists x; P[x]` |
| `exists_elim BLOCK` | export an unpack block's witness-free conclusion |
| `and_intro L R` | conjunction from both conjuncts |
| `and_elim_left STEP` / `and_elim_right STEP` | project a conjunction |
| `or_intro_left STEP` / `or_intro_right STEP` | inject into a disjunction |
| `or_elim DISJ LBLOCK RBLOCK` | case analysis: both assume blocks conclude the claim |
| `not_intro BLOCK S1 S2` | the assumption led to the contradiction `S1`/`S2`, so its negation holds |
| `absurd S1 S2` | from a contradiction, conclude anything |
| `double_negation STEP` | from `not not P`, conclude `P` |
| `reflexivity` | `t = t` |
| `symmetry STEP` | from a proven `x = y`, conclude `y = x` |
| `rewrite EQ TARGET` | replace occurrences of the equation's left side with its right side in `TARGET` |
| `instantiate NAME(args) refs...` | monomorphize a schema; refs discharge its leading antecedents |
| `simplify refs...` | tactic: join both sides of an equation by rewriting (see Automation) |
| `simplify_quantified refs...` | tactic: `simplify` under a `forall` prefix, without a hand `fix` (see Automation) |
| `assoc_commut [(assoc, comm, swap)] [refs...]` | tactic: reorder an associative-commutative sum by its A/C laws — bare uses well-known `add`/`mul`; `(assoc, comm, swap)` supplies the triple for a custom operator; cited refs (e.g. distributivity) pre-normalize first (see Automation) |
| `assoc_commut_quantified [(assoc, comm, swap)] [refs...]` | tactic: `assoc_commut` under a `forall` prefix, without a hand `fix` (see Automation) |
| `assoc(assocLemma)` | tactic: prove `s = t` when equal by **associativity alone** of one operator — right-nests both sides and compares. The associativity lemma is required; no reordering, no commutativity (see Automation) |
| `assoc_quantified(assocLemma)` | tactic: `assoc` under a `forall` prefix, without a hand `fix` (see Automation) |
| `polynomial(theory)` | tactic: prove an `add`/`mul` polynomial identity `s = t` by expanding both sides to a canonical sorted sum of sorted monomials (see Automation) |
| `polynomial_quantified(theory)` | tactic: `polynomial` under a `forall` prefix, without a hand `fix` (see Automation) |
| `tautology refs...` | tactic: propositional consequence (see Automation) |
| `arithmetic refs...` | tactic: linear arithmetic over Nat (see Automation) |
| `model(INSTANCE) source.theorem` | *(forthcoming)* transfer an abstract theory's theorem to a sort that models it, remapped through the named model (see `model` under Declaration keywords) |

## The kernel

The trusted core is deliberately tiny, and everything else is built to
keep it that way.

- **Only concrete first-order logic ever reaches it.** The kernel checks a
  lowered proof: a flat list of steps and blocks, each step carrying its
  formula and justification. It re-derives every rule application itself —
  claim mismatches, inaccessible references, unclosed blocks, and
  eigenvariable violations are all kernel errors.
- **The elaborator is untrusted.** Parsing, name resolution, sort
  checking, schema monomorphization, and every tactic live outside the
  trust boundary. They can only *prepare* steps; the kernel accepts
  nothing on their word (with the single, disclosed exception of accelerated
  steps — see below).
- **Terms are locally nameless.** Bound variables are de Bruijn indices,
  free variables are named and sorted. Substitution can never capture,
  alpha-equivalence is structural equality, and eigenvariable conditions
  are simple occurrence checks.
- **Schemas are checked per instance.** A schema body is stored as a form;
  instantiation substitutes the written-out arguments (capture-proof by
  construction) and produces a concrete formula the kernel can check. A
  theorem schema's stored proof is re-elaborated and re-checked at every
  instantiation.
- **Guards become obligations.** Applying a `requires`-guarded function
  raises a proof obligation, wrapped in whatever logical context surrounds
  the application (binders, antecedents, left conjuncts) and matched
  against facts available where it is owed.

## Automation

Three tactic rules discharge goals in one step. All three follow the same
trust policy, **certificate first, accelerated fallback**:

1. The tactic first tries to emit a *certificate*: ordinary kernel steps
   (rewrites, case splits, witness introductions) synthesized into the
   proof and checked like hand-written ones. A certificated use **emits kernel steps**
   — exactly as trustworthy as a manual proof.
2. Only when the goal is decidable but outside the certificate fragment
   does the tactic reach for its *accelerated* path: the decision procedure's verdict.
   By default this is a **hard error** — the goal must certify. Only under
   `--fast` is the accelerated verdict accepted (without a derivation); its name
   then **marks** the theorem accelerated, transitively through citations, and the
   summary discloses it: `6 theorems proven (1 accelerated:
   arithmetic)` under a loud not-fully-verified banner.

A failed tactic never marks anything accelerated: wrong goals produce located errors
with copy-pasteable detail (unjoinable normal forms, propositional
countermodels, concrete arithmetic counterexamples).

### `simplify` — equational rewriting (always emits kernel steps)

`[by simplify f1 f2 ...]` proves an equation by rewriting both sides to a
common normal form using the cited facts (universally quantified equations
or equation steps) as left-to-right rules. The certificate *is* the
rewrite chain; there is no accelerated path. Cycling rule sets hit a hard rewrite cap
instead of hanging.

```bpa
@succ-case |
  add(succ(k), ZERO) = succ(k)
  [by simplify addSuccLeft inductive-hypothesis]
```

`simplify` proves a bare equation; on a `forall x…; s = t` goal use
`simplify_quantified`, which peels the universal prefix (no hand `fix`),
runs the same core on the body, and closes with `forall_intro`. Each tactic
suggests the other if you pick the wrong one for the goal shape.

### `assoc_commut` — associative-commutative reordering

`[by assoc_commut]` proves `s = t` when both are sums over an associative-
commutative operator with the same multiset of summands, differing only by
associativity and commutativity — including sums whose summands are **arbitrary
opaque terms** (`sumTo(k)`, `mul(k, k)`), which `simplify` cannot reorder (a
commutativity rewrite rule loops) and `arithmetic` treats as opaque and
declines. It re-associates each side to a canonical form and emits the swap
chain as kernel steps; different multisets are a located `assoc_commut: sides
have different summands` error.

```bpa
@swapped |
  add(add(a, b), add(c, d)) = add(add(a, c), add(b, d))
  [by assoc_commut]
```

**Two forms, no partials** — you either supply the whole AC triple or rely on
the well-known one:

- **bare `assoc_commut`** — the operator is chosen from the goal's left-hand-
  side head (`add` or `mul`) and its AC triple (`addIsAssociative`/
  `addIsCommutative`/`addLeftSwap`, or the `mul` triple) is resolved **by
  well-known name in scope**.
- **`assoc_commut(assoc, comm, swap)`** — supply the three AC lemmas
  explicitly, for a **custom operator** whose lemmas aren't named by the
  convention. The operator is recovered from the commutativity lemma's shape
  (`f(a, b) = f(b, a)` → `f`). Exactly three args, or a located error.

```bpa
// a custom operator `join` with its own (non-conventionally-named) AC laws
@reorder |
  join(join(a, b), join(c, d)) = join(join(a, c), join(b, d))
  [by assoc_commut(joinAssoc, joinComm, joinSwap)]
```

**Under a `forall` prefix**, use `assoc_commut_quantified` (peels the binders,
no hand `fix`), the AC analog of `simplify_quantified`.

**Distributivity**: cite rewrite lemmas (e.g. `mulAddDistribRight`) as trailing
refs and `assoc_commut` applies them L→R to each side as pre-normalization
*before* the reorder — so `mul(add(a, b), c) = add(mul(b, c), mul(a, c))`
certifies in one step (distribute, then AC-sort the resulting sum of products):

```bpa
@conclusion |
  forall a, b, c: Nat; mul(add(a, b), c) = add(mul(b, c), mul(a, c))
  [by assoc_commut_quantified mulAddDistribRight]
```

**The `--fast` accelerated path** (bare form only): a theory that declares an operator
but doesn't *prove* its AC laws can't certify — the default declines ("needs
`addIsAssociative` in scope"). Under `--fast`, `assoc_commut` **decides** the
reordering by comparing sorted multisets structurally, WITHOUT resolving any
lemma — **trusting** that the operator is associative-commutative. That
presumption about a symbol whose laws are never checked is why the result is
**accelerated** (`accelerated: assoc_commut`). The explicit-triple form always
certifies (the triple is checkable), so it has no accelerated path.

### `assoc` — associativity-only reordering

`[by assoc(assocLemma)]` proves `s = t` when both are equal by **associativity
alone** of a single operator — the non-commutative sibling of `assoc_commut`.
It right-nests each side (associativity is confluent and terminating, so
right-nesting is a canonical form) and compares; no reordering, no
commutativity. This is what you reach for in **non-commutative** algebra (group
theory: rearranging `(ab)c` ↔ `a(bc)`), where `assoc_commut` does not apply.

```bpa
// a custom group operator `op` with its associativity axiom `opAssoc`
@rearrange |
  op(op(op(a, b), c), d) = op(a, op(b, op(c, d)))
  [by assoc(opAssoc)]
```

**The associativity lemma is REQUIRED** — there is no bare form and no
assumption the operator is `add`/`mul`. `assoc` takes exactly one argument, the
lemma of shape `f(f(a,b),c) = f(a,f(b,c))`, and recovers the operator `f` from
it. This keeps `assoc` fully parameterized by its cited axiom (zero dependence
on ambient scope or well-known names). Bare `[by assoc]` is a located error;
sides that differ by more than associativity report `assoc: sides differ by more
than associativity`. **Under a `forall` prefix**, use `assoc_quantified`.

**The `--fast` accelerated path**: under `--fast`, `assoc` skips *emitting* the rewrite
certificate — it structurally right-nests both sides and compares, presuming the
operator is associative without kernel-checking the rearrangement — and is marked accelerated
(`accelerated: assoc`). By default it certifies (the rewrite chain is checked).

### `polynomial` — nonlinear identities

`[by polynomial(theory)]` proves an `add`/`mul` polynomial identity `s = t`
when both sides expand to the same polynomial — the nonlinear analogue of
`assoc_commut`. It canonicalizes each side to a **sorted sum of sorted
monomials**: distribute `mul` over `add`, sort each monomial's factors, sort the
sum, and fold identity/zero factors. Where `assoc_commut` reorders a sum with a
*fixed* multiset of summands, `polynomial` first *expands* products — so
`(a+b)² = a²+2ab+b²` certifies in one step, which neither `assoc_commut` (it
doesn't distribute the square) nor `arithmetic` (nonlinear, `mul` of two
variables is opaque) can do. It emits a ring-rewrite certificate the kernel
re-checks; different expansions are a located `polynomial: sides expand
differently: '<nf(s)>' vs '<nf(t)>'` error.

```bpa
@square |
  forall a, b: Nat;
    mul(add(a, b), add(a, b)) = add(mul(a, a), add(mul(a, b), add(mul(a, b), mul(b, b))))
  [by polynomial_quantified(peano)]
```

Like `arithmetic`, it is **theory-parameterized**: `polynomial(peano)` resolves
the ring vocabulary (`add`/`mul`) and lemmas against the named upstream module,
independent of local aliases; bare `polynomial` resolves against local scope.
**Under a `forall` prefix**, use `polynomial_quantified` (peels the binders).
Scope: identities only (`=`), whole-number coefficients (ℕ); `succ`-towers are
opaque atoms (unfold `succ(x) = add(x, ONE)` first if a `succ`-shaped identity
must expand), and cancellation (`x·a = x·b ⊢ a = b`) is not an identity — that
stays with `mulCancel`/`arithmetic`.

**The `--fast` accelerated path**: on a theory too thin to certify (`add`/`mul` declared
but the ring lemmas absent), the default declines ("needs `mulAddDistribLeft`
in scope"). Under `--fast`, `polynomial` **decides** the identity by comparing
pure syntactic semiring normal forms — no lemmas consulted — **trusting** that
`add`/`mul` form a commutative semiring. That presumption about symbols whose
laws are never checked is why the result is **accelerated** (`accelerated:
polynomial`). A false identity is still rejected (the accelerated tactic *decides*); the
acceleration is for the unproven ring-structure assumption, not for the comparison.

### `ext` — extensionality-reduction

`[by ext(theory)]` proves an equation `LHS = RHS` between extensional objects
by the *element-chase*: reduce `LHS = RHS`, through the theory's extensionality
lemma, to its pointwise obligation; fix an element; unfold the operators; and
close the residue. It is the mapping/set analogue of `polynomial` — a
**structure tactic, model-parameterized**: the SAME tactic proves set equations
and function equations (and any future extensional theory), selected by the
theory argument. (Prior art: Lean's `ext`.)

```bpa
@intersection-commutes |
  forall a, b: Set; intersection(a, b) = intersection(b, a)
  [by ext_quantified(set)]

@compose-associates |
  forall h, g, f: Fn; compose(compose(h, g), f) = compose(h, compose(g, f))
  [by ext_quantified(function)]
```

It reads the residue's shape to pick its closer: a **set** equation unfolds
`member(x, ·)` via the `<op>Member` lemmas and closes the propositional residue
with `tautology`; a **function** equation unfolds `apply(·, x)` via the
`<op>Apply` lemmas and closes the equational residue with the rewrite join. One
`[by ext…]` line replaces the ~85-line hand element-chase. Like `arithmetic`, it
is **theory-parameterized** (`ext(set)` / `ext(function)` resolve the
extensionality lemma, the `Universe` sort, and the operator lemmas against the
named module); **under a `forall` prefix**, use `ext_quantified`. A false
identity is rejected — the pointwise residue reports a countermodel or the
values differ. It emits kernel steps (its closers do), so uses are kernel-checked.

### `tautology` — propositional consequence

`[by tautology refs...]` proves any goal that follows propositionally from
the cited premises, treating non-propositional subformulas as opaque
atoms. Valid goals replay as certificates (case splits via an inline
excluded middle); non-consequences report a countermodel
(`countermodel: p := true, q := false`). Atom limit: 16.

### `arithmetic` — linear arithmetic over Nat

`[by arithmetic refs...]` decides goals over `ZERO`, `ONE`, `succ`, `add`,
`mul`-by-literal, `=`, `!=`, and `less_than`, with full propositional
structure and quantifiers over Nat; anything else becomes an opaque
propositional atom in an SMT-style combination. The vocabulary is
recognized by those well-known names in the current scope, and
certificates additionally use the standard peano lemmas
(`addZeroRight`, `addIsCommutative`, `addLeftSwap`, `lessThanIntro`,
`lessThanElim`, ...) when they resolve — import them from `std/peano.bpa`
to keep uses emitting kernel steps. Certificates cover ground and universally quantified
linear goals, order goals, constant-witness existentials, hypothesis
chains, and mixed skeletons; goals whose replay would itself require
induction fall back to the accelerated path. False statements report concrete
values: `arithmetic: false at a := 0, b := 0`; a relation that is only
undecidable because it hides a nonlinear term (e.g. `mul(a, b) = mul(b, a)`)
reports `'mul(a, b)' is outside linear arithmetic` rather than a countermodel.

```bpa
@conc-in |
  less_than(a, succ(b))
  [by arithmetic have]
```

> [!WARNING]
> This may be expanded in the future to support signed integers (exact, as
> everything in bpa).

The full trust statement for each accelerated tactic — module, verdict semantics,
certificate coverage — lives in `ACCELERATION.md`.

## Query commands (read-only inspection)

`bpa query <op>` inspects `.bpa` files (and `.md` literate documents — the
`bpa` blocks are extracted the same way `check` does) without checking them,
for navigating a proof corpus. grep is the right tool for most searches (label
audits, "who uses `[by arithmetic]`", counting); these cover the cases grep
can't do cleanly.

| Command | What it does |
|---|---|
| `bpa query outline <file> [theorem]` | the proof *skeleton*: one line per step (bare label), with a header on each block opener (`fix`/`assume`/`unpack`/`case`). No theorem arg = every proof in the file. |
| `bpa query theorem <file> <name> [--sig]` | the full verbatim source of one declaration — statement + `proof … qed` + leading doc-comment. Follows aliases across files to the real proof; axioms are marked. `--sig` prints **just the statement** (kind + name + formula), wrap-collapsed to one line — handy for reading binder order/arity before a `forall_elim`. |
| `bpa query whereis <file> <identifier>` | trace an identifier through every alias/import hop to its **origin** — the file-chase as one command. Works for any named decl (theorem/axiom/func/pred/sort/const/define/schema) and for import namespaces. Each hop shows `file:line` + the source line; the origin is marked. |
| `bpa query search <path> <query>` | fuzzy-search theorem/axiom **names + statements** — find a lemma by concept when you don't recall its name (`search std cancel` → `mulCancelLeft`, `addCancelLeft`, …). `<path>` is a **directory** (search every `.bpa` under it — corpus discovery) or a **file** (search it + everything it transitively imports — only results citable from there). Ranked, one line per hit: `file:line  <kind> <name>: <statement>`. Query terms are AND'd. Self-contained/deterministic (no ML). |

```
$ bpa query whereis std/peano-parity.bpa addZeroRight
addZeroRight
  std/peano-parity.bpa:30:  theorem addZeroRight = peano.addZeroRight
  std/peano.bpa:79:  theorem addZeroRight: forall n: Nat; add(n, ZERO) = n  [origin]
```
