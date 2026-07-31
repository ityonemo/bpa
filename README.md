# bpa

A proof checker written in Zig. It consumes `.bpa` files containing
declarations and proofs, verifies every step, and reports either a summary
line or precise `file:line:col` diagnostics.

The language design optimizes for clarity under constrained (human and llm)
context: proofs are explicit named steps, every name is greppable, diagnostics are
copy-pasteable surface syntax, and checking is fully deterministic.

## Design

**Explicit.** A proof is a sequence of named steps; every step states its
formula in full and names the rule and references that justify it. There is
no proof search, no hidden state, and no implicit context: what you read is
exactly what the checker checks. Where automation exists, it is a rule you
invoke explicitly, and its work is either replayed as ordinary checked
steps or disclosed.

**Optimized for LLMs and humans alike.** Both audiences read the same
surface: names are greppable (`grep 'by axiom'` is an assumption audit),
diagnostics re-parse verbatim as source, connectives are words rather than
symbol soup, and libraries of schematic statements cost nothing until used
— so context stays small and feedback stays precise. Layout is generous on
purpose; the tokens are thinking room.

**Inspired by Zig.** Beyond being the implementation language, the core
idea is borrowed from Zig's `comptime`:

```
axiom induction(prop: Nat -> Prop):
  prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)
```

behaves like `fn List(comptime T: type)`: it the case of bpa it is a **stored form**,
not a theorem. It does nothing until instantiated with a concrete,
written-out argument, at which point it is monomorphized into plain
first-order logic.  A theorem schema's proof is re-checked at each
instance, just as Zig re-analyzes a generic function per instantiation.

**Why schematics instead of higher-order logic.** Quantifying over
predicates is what makes proof assistants heavy: higher-order unification,
undecidable matching, large trusted cores. But almost every practical use
of that power is *instantiating* a general rule with a predicate you
supply. bpa keeps exactly that half: schemas are instantiated only with
formulas you have actually written down, so instantiation is decidable
substitution rather than search, no quantifier over predicates ever exists
in the object logic, and the trusted kernel stays a few hundred lines of
concrete first-order checking.

**Mistakes fail loud, never silent.** You can still write a *bad proof* —
an awkward detour, a cited step that doesn't apply, a tactic pointed at the
wrong goal. What you cannot do is have such a mistake yield a false theorem.
The worst case for a usage footgun is a located `file:line:col` error, not a
wrongly-accepted result. This is a structural property, not a promise of
care: the kernel re-derives every rule application itself and trusts nothing
the elaborator, parser, or a tactic asserts. There are exactly two claims
the kernel accepts without re-deriving — a schema *instance* (and it still
checks the premise-matching) and a named *oracle* verdict — and both are
made visible rather than hidden: an oracle taints its theorem, the summary
line discloses it, and `bpa check --pure` rejects it outright. Ambiguity is
squeezed out of the surface for the same reason: `:` is only ever sort
ascription, `|` only ever a step label, connectives are words not symbols,
and no-shadowing is enforced — so a proof reads one way, and the way it
reads is the way it is checked.

## Quick start

```
zig build
./zig-out/bin/bpa check examples/peano.bpa
```

```
OK: 18 declarations, 6 theorems proven (5 pure, 1 via oracles: arithmetic)
```

A proof is a sequence of labeled steps, each justified by a rule:

```
sort Nat
const ZERO: Nat
func succ(n: Nat): Nat
func add(a: Nat, b: Nat): Nat
axiom addZeroLeft: forall b: Nat; add(ZERO, b) = b
axiom addSuccLeft: forall a, b: Nat; add(succ(a), b) = succ(add(a, b))

define TWO = succ(succ(ZERO))
define FOUR = succ(succ(TWO))

theorem twoPlusTwo: add(TWO, TWO) = FOUR
proof
  @conclusion |
    add(TWO, TWO) = FOUR
    [by arithmetic]
qed
```

Failures are located and exact:

```
$ ./zig-out/bin/bpa check examples/incorrect.bpa
examples/incorrect.bpa:35:39: error: modus_ponens: expected antecedent 'raining', got 'wet'
```

## How it works

- A **tiny trusted kernel** checks concrete first-order logic: every proof
  step names a rule and the steps it depends on, and the kernel verifies
  each one. Everything outside the kernel — parsing, name resolution,
  tactics — is untrusted machinery that can only ever *prepare* work for
  it.
- **Schematic statements** are stored forms, monomorphized per
  instantiation (see Design above); the kernel only ever sees the concrete
  first-order instances.
- **Automation is certificate-first.** The `simplify`, `tautology`, and
  `arithmetic` rules discharge goals in one step. Whenever possible they
  emit ordinary kernel steps (a *certificate*), so the result is exactly as
  trustworthy as a hand proof. When a decidable goal falls outside the
  certificate fragment, a built-in decision procedure (an *oracle*) accepts
  it, the theorem is marked, and the summary line discloses it. `bpa check
  --pure` rejects every oracle-backed step.
- **Imports** (`import peano <<< "std/peano.bpa"`) bring in namespaced
  declarations; `--recursive` re-verifies imported proofs.  Note that the
  default reverification strategy may be revisited in the future to prevent
  footguns.

## Compared to other proof assistants

bpa is young and deliberately narrow; the mature systems below are vastly
more capable and have decades of libraries. These sections are about
*design differences*, not a claim that bpa competes on power. The recurring
theme: bpa trades expressive foundations for a tiny kernel, decidable
elaboration, and an explicit surface — a trade that suits a proof *checker*
whose proofs are written to be read (by humans and LLMs) and grepped.

Each subsection below names a **footgun** that system has and bpa does not —
a place where the more powerful design admits a hazard the narrower one
rules out by construction. These are genuine trade-offs the other systems
made knowingly for good reasons, not defects; the point is only to show what
bpa's constraints buy.

One footgun is shared by all three, so it goes here: **division (and other
partial functions) is made *total* by fiat.** Lean, Isabelle/HOL, and Rocq
all define `n / 0 = 0` (and `head []`, etc.) so the term is well-typed —
which means `n / 0` silently denotes a meaningless value and a proof can pass
through it without anyone noticing the degenerate case. bpa instead guards
such functions (`func div(a, b) requires b != ZERO`), turning every use into
a proof obligation: you must *prove* the divisor is nonzero, or the check
fails with a located error. The cost is that you carry the obligation; the
benefit is that the `n / 0` case cannot silently slip into a proof.

**A caveat about the sections below, and where bpa is headed.** Each section
names a place where those systems trust a compiler, VM, or code generator the
kernel does not re-check. bpa does **not** today escape this class of trust:
when `arithmetic` cannot yet produce a certificate it falls back to an oracle
— a step accepted with no derivation, resting on bpa's own decision procedure
(the Cooper-algorithm implementation in `src/presburger.zig`) rather than the
kernel. That code is **young and only lightly tested** — a handful of
fixtures and unit tests, far less exercised than the hardened evaluators
those systems ship — so per oracle use it is, if anything, *more* likely to
harbor a bug. This is stated plainly because the design already makes it
impossible to hide, and because it is a **transitional** state, not the
intended one.

The roadmap inverts the relationship with oracles entirely
(`CERTIFICATES-PLAN.md`):

- **Certificate-by-default.** The direction of travel is that `by arithmetic`
  *produces a full kernel-checked proof* by default; the oracle becomes a
  genuine last resort for the one fragment that is provably hard to certify
  (quantifier-alternation replay), not a fallback proofs drift into. Most of
  the linear fragment is already certificated; the largest remaining lever is
  a **Farkas certificate** for linear infeasibility, a fixed no-search recipe
  that turns the bulk of remaining oracle uses pure in one step.
- **A loud, opt-in fast mode for development.** A `--fast` flag will *skip*
  certificate generation and take the oracle verdict, for quick iteration
  while a proof is still being worked out — announced in the summary, never
  silent, and the thing you turn *off* before finalizing. Paired with the
  existing `--pure` (certificate-or-error, no oracle ever), that is a
  three-point spectrum: `--pure` ⟶ default (certificate-preferred) ⟶
  `--fast`.

So the honest claim in each section below is narrow but real, and it holds
today *and* strengthens over time: not that bpa trusts *less code* in the
worst case, but that whatever it trusts beyond the kernel is **named,
transitively propagated, printed on every summary line, and refusable with
`--pure`** — never silent, never discoverable only by after-the-fact audit —
and that the amount so trusted is on a deliberate path toward zero for
everything short of the undecidable fragment.

### Lean vs bpa

Lean is a dependently-typed proof assistant and a full programming language:
its logic is the Calculus of Inductive Constructions, proofs *are* programs
(terms of a type), and `Prop` is one universe among many. Its kernel is
small by dependent-type standards but still implements definitional equality,
universe checking, and inductive families. Lean's automation (`simp`,
`omega`, `decide`, and the Mathlib tactic ecosystem) is powerful and
tactic-block-oriented; a Lean proof is typically a script whose intermediate
states you inspect in an editor rather than a document you read top to bottom.

bpa is many-sorted **first-order** logic — no dependent types, no `Type`
universes, no proofs-as-programs. That is a real expressiveness ceiling
(you cannot, e.g., index a type by a value). In exchange the kernel checks
only concrete FOL in a few hundred lines with no definitional-equality
engine, "higher-order" reasoning is the `comptime`-style schema mechanism
(decidable instantiation, never higher-order unification), and every proof
is an explicit sequence of named steps that reads as a static artifact. Where
Lean reaches for a powerful trusted elaborator, bpa keeps the trusted base
minimal and makes each automation either replay as checked steps or disclose
itself as an oracle.

*Where bpa differs:* the trusted base growing **silently**. `native_decide`
discharges a decidable goal by compiling its `Decidable` instance to native
code, running it, and believing the answer — so the proof's soundness now
rests on the Lean compiler, the runtime, and the `Lean.ofReduceBool` /
`trustCompiler` assumptions ("if the compiled `Bool` reduces to `true`, it
*is* `true`"), none of which the kernel checks. Unlike `sorry`, this is meant
to be used in real proofs — it is the fast path when `decide` is too slow —
so a user aiming at a genuinely correct proof can inherit the whole compiler
as a trust dependency without realizing it, and `native_decide` has in fact
been used to derive `False` through compiler and FFI bugs. The exposure is
visible only if you run `#print axioms` and know to look. bpa is **not** free
of this class of trust — its oracles are exactly the same kind of
accept-without-a-derivation (see the shared caveat above) — but the trust is
never silent: it taints the theorem, prints on the summary line, and
`--pure` rejects it, so "am I relying on something the kernel didn't check?"
is answered by default rather than by an after-the-fact audit.

### Isabelle/HOL vs bpa

Isabelle/HOL is built on higher-order logic (simply-typed lambda calculus
with `bool`) atop the generic Isabelle framework. Its defining strength is
the **LCF architecture**: theorems are an abstract type produced only by a
small trusted inference kernel, so even elaborate automation (the classical
reasoner, `auto`, `sledgehammer` dispatching to external provers) is
sound by construction — everything ultimately factors through kernel
inferences. Isabelle proofs are often written in Isar, a structured,
readable proof language.

bpa shares Isabelle's instinct that the trusted core should be tiny and that
automation should reduce to kernel-checkable steps — bpa's certificate-first
tactics are the same idea (an `omega`-style result that replays as ordinary
rules is "pure", exactly as an Isabelle tactic factors through the kernel).
The differences: bpa is first-order rather than HOL, so it has no genuine
quantification over predicates (the schema mechanism substitutes for the
common *instantiation* case only); and bpa is explicit about the cases where
a decision procedure *cannot* be replayed — those become disclosed oracles
with `--pure` to reject them, rather than being trusted silently. Isar and
bpa's step language share the "proof as a readable document" goal; bpa's is
smaller and more rigid, tuned for greppability and constrained context.

*Where bpa differs:* how the analogous trust is surfaced. Isabelle's `eval`
method (and `value`) proves a proposition by having the code generator emit
ML, compiling it, and running it — so the result is trusted on the code
generator, the ML compiler, and the runtime, outside the LCF kernel. As with
Lean's `native_decide` this is a legitimate performance tool aimed at real
proofs, not a stub. Isabelle is honest about it — it can track such
derivations and offers the slower kernel-checked `code_simp` — and bpa's
oracle is the same shape of accept-without-a-derivation, so bpa is not
categorically cleaner here. What bpa fixes is default and enforcement: an
oracle use is *always* a named, transitive taint on the theorem, on the
summary line, with `--pure` to refuse it — you don't have to know to check.

### Rocq (Coq) vs bpa

Rocq (formerly Coq), like Lean, is founded on the Calculus of Inductive
Constructions with dependent types and proofs-as-programs, and it pioneered
much of that tradition (the kernel, `Ltac`/`Ltac2` tactic languages,
extraction to executable code, and landmark developments like CompCert and
the Feit–Thompson proof). A Rocq proof is a tactic script producing a proof
term the kernel type-checks; the kernel is small but implements the full
dependent-type conversion check.

bpa makes the same trade against Rocq as against Lean — no dependent types
and no proofs-as-programs, so no extraction and a hard expressiveness limit,
in return for a first-order kernel with no conversion engine and a proof
format that is a plain checked step list rather than a tactic script. One
narrower point of contact: Rocq's `Ltac` is a Turing-complete *untrusted*
metaprogramming layer that emits proof terms the kernel re-checks — bpa's
tactics occupy the same "untrusted, must produce kernel-checkable output"
role, but they are fixed built-in procedures rather than a user
metaprogramming language, and bpa additionally formalizes the escape hatch
(an oracle) for results the kernel genuinely cannot re-derive.

*Where bpa differs:* the same compiled-reduction trust surface as Lean
appears in Rocq's own form. `native_compute` compiles terms to OCaml, runs
them, and trusts the result to close a goal by computation; `vm_compute` uses
a bytecode VM inside the kernel's reduction. Both fold the compiler or VM
into the trusted computing base — Rocq's documentation flags `native_compute`
as doing exactly that — so a proof closed this way for speed depends on more
than the type theory, discoverable only via `Print Assumptions` / careful
audit. bpa does not escape the category (its oracles are the analogue), but
it removes the *silence*: no compiled fast path sits in the trusted position
unnamed. Every unchecked step is a disclosed, `--pure`-rejectable oracle, and
the trusted surface stays statable in a sentence — the FOL kernel, its two
disclosed elaborator licenses, and whatever oracle code a given proof's taint
names.

## Layout

| Path | Contents |
|---|---|
| `examples/peano.bpa` | the living demo: automation-assisted Peano arithmetic |
| `examples/peano-pure.bpa` | the same theory proved entirely by hand |
| `examples/gauss.bpa` | Gauss's summation formula (with the `assoc_commut` tactic) |
| `examples/euclid.bpa` | Euclid's gcd, consuming the verified `std/peano-gcd` library |
| `examples/euclid-compute.bpa` | gcd *run* on concrete numbers: `gcd(9, 6) = 3`, unfolded step by step |
| `examples/incorrect.bpa` | three classic wrong proofs and their diagnostics |
| `examples/sqrt2.bpa` | **√2 is irrational** (stated over ℕ), proved pure |
| `examples/literate.md` | a **literate** proof: prose + checkable ` ```bpa ` blocks |
| `std/` | the standard library: arithmetic (`peano`), order + strong induction (`peano-ordering`), subtraction, division/divisibility, the verified `peano-gcd`, even/odd + the parity crux (`peano-parity`), abstract group theory (`group`), and set algebra over a universe (`set`) |
| `aata/` | **literate transliterations of an abstract-algebra textbook** (Judson's AATA, GFDL) verified in bpa — the book's prose reproduced in order, each stated result followed by a checked proof; see `aata/README` |
| `GUIDE.md` | every keyword, the kernel design, the built-in oracles |
| `CONVENTIONS.md` | naming and proof-writing style |
| `ORACLES.md` | the oracle registry and trust disclosure |

## Commands

```
bpa check [--fast | --faster | --reckless] <file.bpa | file.md>
bpa fmt [--check] <file.bpa>
bpa query outline  <file> [theorem]
bpa query theorem  <file> <name> [--sig]
bpa query whereis  <file> <identifier>
bpa query search   <file|dir> <query>
```

`check` verifies a file and everything it imports. By default it verifies
everything; the speed flags defer work during development and say so loudly
(`--fast` accepts oracle verdicts, `--faster` also trusts imported proofs,
`--reckless` also trusts imported schemas). Re-run plain `bpa check` to
finalize. `fmt` normalizes whitespace and indentation in place (`--check`
reports instead of rewriting).

### Literate proofs (`.md`)

`check` also runs on **Markdown**: give it a `.md` file and it verifies the
proofs inside ` ```bpa ` fenced code blocks, ignoring the prose. All the code
blocks in a document share one scope (a later block may cite a theorem from an
earlier one), and errors report the line number **in the `.md` itself** — so a
literate proof document is a first-class, checkable artifact. See
`examples/literate.md`.

```
$ bpa check examples/literate.md
OK: 6 declarations, 1 theorems proven
```

The `bpa query` commands (below) also understand `.md` — they extract the same
`bpa` blocks — so you can outline, look up, or search proofs written literately.

### Query (read-only inspection)

`bpa query` navigates a proof corpus without checking it — for the cases plain
`grep` handles poorly: a proof's *structure*, a theorem's *exact statement*
(which may wrap across lines), *following an alias across files*, or *finding a
lemma by concept* when the name is fuzzy.

- `query outline <file> [theorem]` — the proof **skeleton** (one line per step,
  with headers on `fix`/`assume`/`unpack`/`case`).
- `query theorem <file> <name> [--sig]` — a declaration's full source, aliases
  followed to the origin; `--sig` prints just the one-line statement (handy for
  reading binder order before a `forall_elim`).
- `query whereis <file> <identifier>` — trace an identifier through every
  alias/import hop to its **origin**.
- `query search <file|dir> <query>` — fuzzy-search theorem/axiom names +
  statements (a directory searches the whole corpus; a file searches its
  transitive-import scope).

For plain text searches (label audits, tactic-usage sites, counts), use `grep`.

Exactness is a hard rule: bpa works symbolically, and where it computes it
computes with exact integers. There are no floating-point numbers anywhere,
ever.
