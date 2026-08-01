---
name: bpa-query
description: Inspect and navigate a bpa proof corpus (.bpa files) with the `bpa query` commands — outline a proof's structure, print a theorem's full source or one-line signature, trace an identifier to its origin across alias/import hops, or fuzzy-search for a lemma by name/concept. Use these BEFORE grepping for anything that involves a proof's shape, a theorem's exact statement/binder-order, following an alias to another file, or finding a lemma when you don't recall its name. For plain text searches (label audits, "who uses [by X]", counts) prefer grep — these tools cover only what grep can't do cleanly.
---

# bpa query — navigating a proof corpus

`bpa query <op>` reads `.bpa` files (and `.md` literate documents — the ```bpa
blocks are extracted, like `check`) without checking them, for navigation. Build
the binary first if needed (`zig build`); it lands at `./zig-out/bin/bpa`.

**Guiding principle: we love grep.** grep/sed/awk are the default for text
searches over the corpus — label audits (`grep -rhoE '@[a-z-]+' std/*.bpa`),
"who uses `[by arithmetic]`" (`grep -rn '\[by arithmetic\]'`), counts, listing
`^theorem`/`^forward`. Reach for `bpa query` ONLY for the things grep does
badly: a proof's *structure*, a theorem's *exact statement* (which may wrap
across lines), *following aliases across files*, or *finding a lemma by concept*
when the name is fuzzy. Each command below exists precisely because grep can't
do that one thing easily or in one step.

## The four commands

### `bpa query outline <file> [theorem]`
The proof **skeleton**: one line per step (bare label), with a header on each
block opener (`fix`/`assume`/`unpack`/`case`). No theorem arg → every proof in
the file. Use to grasp a proof's shape without reading the whole body.

```
$ bpa query outline std/peano.bpa addZeroRight
theorem addZeroRight
  add-zero-left
  base-case
  induction-step  fix k
    given-inductive-hypothesis  assume add(k, ZERO) = k
      ...
  conclusion
```

### `bpa query theorem <file> <name> [--sig]`
The full verbatim source of one declaration — statement + `proof … qed` + its
leading doc-comment. **Follows aliases across files** to the real proof; axioms
are marked. `--sig` prints **just the statement** (kind + name + formula),
wrap-collapsed to one line — the fast way to read **binder order / arity before
a `forall_elim`** (its args are outermost-first, and the statement may wrap in
source, so grep+head is unreliable).

```
$ bpa query theorem std/peano-ordering.bpa multiplicationPreservesOrder --sig
theorem multiplicationPreservesOrder: forall c, b, a: Nat; less_than(a, b) -> less_than(mul(succ(c), a), mul(succ(c), b))
```

### `bpa query whereis <file> <identifier>`
Trace an identifier through every alias/import hop to its **origin** — the
file-chase as one command (grep finds one hop; you'd re-grep per hop). Works for
any named decl (theorem/axiom/func/pred/sort/const/define/schema) and for import
namespaces. Each hop shows `file:line` + the source line; origin marked.

```
$ bpa query whereis std/peano-parity.bpa addZeroRight
addZeroRight
  std/peano-parity.bpa:30:  theorem addZeroRight = peano.addZeroRight
  std/peano.bpa:79:  theorem addZeroRight: forall n: Nat; add(n, ZERO) = n  [origin]
```

### `bpa query search <path> <query>`
Fuzzy-search theorem/axiom **names + statements** — find a lemma by concept
when you don't recall its name. `<path>` is a **directory** (every `.bpa` under
it — corpus discovery) or a **file** (that file + everything it transitively
imports — only results citable from there). Query terms are AND'd; ranked by
name-exact > name-substring > statement-token. One line per hit. Self-contained
and deterministic (no ML — semantic search is a future, caching-era upgrade).

```
$ bpa query search std cancel
std/peano-ordering.bpa:1960:  theorem mulCancelLeft: forall c, a, b: Nat; c != ZERO -> mul(c, a) = mul(c, b) -> a = b
std/peano.bpa:1210:  theorem addCancelLeft: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
...
```

## Typical workflow

Writing a proof and need a lemma:
1. `bpa query search std <concept>` — find candidates by name/statement.
2. `bpa query theorem <file> <name> --sig` — read its exact statement + binder
   order before citing it in a `forall_elim`.
3. `bpa query whereis <myfile> <name>` — if it's aliased, see where it really
   lives (and confirm it's reachable from your file's scope).
4. `bpa query outline <file> <similar-theorem>` — model your proof's structure
   on an existing one.

For everything textual (labels, tactic-usage sites, counts), just grep.
