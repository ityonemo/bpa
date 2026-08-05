---
paths:
  - "**/*.bpa"
  - "aata/**/*.md"
  - "examples/**/*.md"
---

# bpa cheat-sheet (dense)

The load-bearing mechanics + gotchas for writing `.bpa` proofs, in one page.
`GUIDE.md` is the comprehensive reference; this is the lookup you keep in head.
For depth on one thing, extract its GUIDE section (leaf sections are bounded by
the next heading of any level):

```
awk '/^#+ /{p=0} /^### RULE: or_elim$/{p=1} p' GUIDE.md      # a proof rule
awk '/^#+ /{p=0} /^### TACTIC: tautology$/{p=1} p' GUIDE.md  # an accelerant
awk '/^#+ /{p=0} /^### KEYWORD: sort$/{p=1} p' GUIDE.md      # a declaration keyword
```

Naming/label conventions are a SEPARATE doc — see `agents/style-guide.md`.

## Proof skeleton

```bpa
theorem foo: forall a: Nat; P(a)
proof
  @generalize-a |
    fix a: Nat {
      @some-fact | <formula> [by axiom someAxiom]
      @conclusion-inner | P(a) [by ...]
    }
  @conclusion | forall a: Nat; P(a) [by forall_intro generalize-a]
qed
```

- Every step is `@label | <formula> [by <rule> <refs>]` (label, formula, justification — the formula and `[by …]` indented two spaces under the label). Blocks nest two spaces.
- A `fix x: S { … }` block generalizes; a SEPARATE `forall_intro <block-label>` step discharges it (the block is not itself the universal). Same for `assume F { … }` + `implies_intro`.
- Inside an `assume F { … }` block, restate the assumption with `[by hypothesis <block-label>]`. Inside a `fix h: H` (refined sort), get its guard `inH(h)` with `[by predicate <block-label>]`.
- Refs are SPACE-separated: `[by and_intro a b]` NOT `a, b`.
- Term arguments go in parens on the rule: `[by forall_elim(succ(b)) some-step]`.

## Proof rules — EXACT ref counts (the drift-prone part)

| rule | refs | notes |
|---|---|---|
| `axiom NAME` / `theorem NAME` | 0 (names a stmt) | must introduce a cited axiom/theorem AS A STEP before a later `forall_elim` references it — `@a \| forall …; … [by axiom foo]` then `forall_elim(t) a` |
| `hypothesis BLOCK` | 1 block | restate an enclosing assume/unpack assumption |
| `predicate FIXBLOCK` | 1 block | guard `inH(h)` of a refined `fix h: H` |
| `modus_ponens IMP ANT` | 2 | order: implication FIRST, antecedent second |
| `implies_intro BLOCK` | 1 block | discharge `assume` → implication |
| `forall_intro BLOCK` | 1 block | discharge `fix` → universal |
| `forall_elim(t, …) STEP` | 1 step (+ term args) | multi-arg peels several binders in one step |
| `exists_intro(t) STEP` | 1 step (+ witness term) | |
| `exists_elim BLOCK` | 1 block | export an `unpack` block's witness-free conclusion |
| `and_intro L R` | 2 | REJECTS a biconditional-shape goal `(X->Y) and (Y->X)` — use `iff_intro` |
| `and_elim_left STEP` / `and_elim_right STEP` | 1 | |
| `iff_intro FWD BWD` | 2 | forward `P->Q` then backward `Q->P`; goal must be `P iff Q` shape |
| `iff_elim_forward STEP` / `iff_elim_backward STEP` | 1 | recover `P->Q` / `Q->P` from `P iff Q` |
| `or_intro_left STEP` / `or_intro_right STEP` | 1 | |
| **`or_elim DISJ LBLOCK RBLOCK`** | **3 (1 step + 2 blocks)** | **BINARY only.** A 3-way split needs `case on <disj> { … }` (see below), NOT a 3-ref or_elim |
| `not_intro BLOCK S1 S2` | 3 (1 block + 2 steps) | the block's assumption yielded contradiction S1/S2 |
| `absurd S1 S2` | 2 | from a contradiction, conclude anything |
| `double_negation STEP` | 1 | `not not P` → `P` |
| `reflexivity` | 0 | `t = t` |
| `symmetry STEP` | 1 | `x=y` → `y=x` |
| `rewrite EQ TARGET` | 2 | replace EQ's lhs by rhs in TARGET |
| `iff_rewrite BICOND TARGET` | 2 | from `P iff Q`, replace sub-prop P by Q in TARGET (any position). Kernel-checked, no taint |
| `instantiate NAME(args) refs…` | schema + premise refs | monomorphize a schema; refs discharge its leading antecedents |

`case on <disj-step> { @when-left| assume A { … } @when-right| assume B { … } }` — the 3-way (or N-way) disjunction eliminator. Use this instead of trying to give `or_elim` more than 2 arms.

## Formula syntax edges

- Connectives are WORDS: `and`, `or`, `not`, `->` (right-assoc), `iff` (lowest precedence). No `<->` symbol — it's the keyword `iff`.
- **Mixed boolean operators need explicit parens.** Same-op chains are fine (`a or b or c`, `a -> b -> c`); DIFFERENT ops must be parenthesized: `a and b or c` is a parse error → `(a and b) or c`. This includes `not` as an operand (`(not p) and q`, `a -> (not b)`) and `iff` (`(a and b) iff c`, `a -> (P iff Q)` — an iff under `->` needs parens).
- `=` / `!=` are term comparisons, NOT boolean ops — never need parens against a connective (`x = y and p` parses as `(x = y) and p`).
- Quantifier binders end with `;`: `forall a, b: Nat; …`, `exists w: Nat; …`.
- No infix minus, ever — write `sub(a, b)`.

## iff (surface sugar)

`P iff Q` desugars to `(P -> Q) and (Q -> P)`; the kernel never sees `iff`. Therefore:
- Prove with `iff_intro fwd bwd`; eliminate with `iff_elim_forward` / `iff_elim_backward`.
- `tautology` DECIDES `iff` goals and CONSUMES `iff` hypotheses for free (it sees the desugared conjunction).
- `iff_rewrite BICOND TARGET` substitutes P↔Q across a goal (subformula congruence).
- The shape `(X -> Y) and (Y -> X)` is CANONICALLY an iff: `and_intro` refuses it (use `iff_intro`), `iff_intro` requires it. So write biconditionals as `iff`, not hand-rolled conjunctions.

## Accelerants (tactics) — one-liners; detail at `### TACTIC: <name>` in GUIDE.md

- `simplify` — equational rewriting to a shared normal form (always emits kernel steps).
- `assoc_commut` / `assoc_commut_quantified` — reorder an A/C sum; bare = add/mul, `(assoc,comm,swap)` for a custom op; `_quantified` peels a `forall` prefix.
- `assoc(assocLemma)` — associativity-ONLY equality (required lemma arg; no commutativity).
- `polynomial(theory)` — nonlinear `add`/`mul` identity by canonical expansion.
- `ext` — extensionality reduction (sets/functions) → propositional residue.
- `tautology refs…` — propositional consequence (decides iff goals; consumes iff/`and`/`or`/`->` hyps). Atom cap 16.
- `arithmetic refs…` — linear arithmetic over Nat (Presburger). `arithmetic(module)` / `fallback(thm)` variants.
- Discipline: in `std/*.bpa` use accelerants freely (shortest kernel-checked proof). In `aata/*.md` do NOT accelerate a step Judson spells out — transcribe it; accelerants only for algebra the book elides. (See `.claude/rules/aata-guide.md`.)

## Declaration keywords — one-liners; detail at `### KEYWORD: <name>` in GUIDE.md

`sort` (a type; `sort H = G where inH` is a refined subsort), `const` (0-ary), `func` (returns a term-sort, never Prop), `pred` (opaque predicate; no `:=` body), `axiom`, `theorem`, `hole` (aspirational placeholder — a top-level DECLARATION, NOT a `[by hole]` step; default rejects, `--draft` allows), `forward` (declare-before-prove), `import X <<< "path"`, aliases (`sort A = X.B`, `func f = X.g`), `model NAME { src: tgt … }` (discharge an abstract theory's axioms so its theorems transfer; cite `[by model(NAME) src.thm]`).

## Gotchas that bite (memorize)

- `[by hole]` is INVALID — `hole` is a top-level declaration, not a justification. Every obligation must really be proved (or the theorem itself is a `hole`).
- `or_elim` is BINARY. 3-way → `case on`.
- Cite a theorem/axiom as a `[by theorem X]` / `[by axiom X]` STEP before a later `forall_elim` refs that step.
- No `<->`; use `iff`. No `<->`-style iff intro/elim beyond `iff_intro`/`iff_elim_forward`/`iff_elim_backward`.
- A `func` cannot return `Prop` and cannot take a `-> Prop` parameter; predicates are opaque (no body).
- No variable shadowing (checker-enforced). When generalizing a statement binder, reuse the statement's binder name.
- A declarations-only file (no `theorem`s) checks with an informational note + exit 0 — that's fine, it's a dependency. A file that declares theorems but a proof fails is a hard error.
