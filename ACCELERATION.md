# Accelerated-tactic registry

An **accelerated tactic** is a decision procedure whose verdict the checker can
accept without a kernel derivation. Accelerated tactics are the deliberate
exception to bpa's otherwise-closed trust story: the kernel checks every
ordinary step, but an `.accelerated` step stands on the named procedure being
correct. Each invocation either **emits kernel steps** (a full chain of
kernel steps, staying kernel-checked) or **accelerates** (it trusted the procedure without a chain).

The trust is disclosed, never silent:

- every accelerated step **marks** its theorem accelerated with the tactic's
  name;
- citing an accelerated theorem (directly, via `simplify` rules, as a
  `tautology` premise, or through a schema instantiation whose proof cites one)
  inherits the accelerated-tactic names **transitively**;
- the summary line reports the split, e.g.
  `OK: 9 declarations, 5 theorems proven (4 accelerated: tautology)`;
- by default `bpa check` **rejects every accelerated step with a located
  error** — the goal must be kernel-checked. The accelerated verdict is accepted only
  under `--fast` (which then discloses it under a loud accelerated banner).

Under `--faster`/`--reckless`, imported theorems are *trusted* (their proofs
are not re-checked), which supersedes any acceleration disclosure; the summary
reports those separately.

Tactics are **certificate-first**: an invocation that can emit ordinary
kernel steps does so and stays kernel-checked. Certificates are produced by an
ordered **certifier chain** (equation/order/exists → mixed-skeleton → Farkas →
future Cooper-replay/manual), walked first-success-wins; each link either
emits kernel steps or **declines with a reason**. When every link declines,
the default is a hard error listing each link's reason (so a valid goal on a
thin theory names the missing symbol/lemma to add — an actionable fix, not
"write a manual proof"); `--fast` accepts the accelerated verdict for that
goal, marking that use accelerated only. Certificate stages grow over time,
monotonically shrinking what needs `--fast` with no surface change.

The same elaborate-by-default / `--fast`-accelerated split applies to the
equational tactics `polynomial` and `assoc_commut` (below): their default path
emits kernel-checked rewrites citing the theory's proven ring/AC lemmas, and
only `--fast` presumes the vocabulary's algebra structurally and accelerates. A
tactic is acceleration-shaped precisely when it depends on a well-known stdlib
function and presumes its behavior — the acceleration discloses that
presumption; the theory argument (`polynomial(peano)`, `arithmetic(peano)`)
pins it to a vetted theory.

## Registered accelerated tactics

### `tautology` — propositional consequence

- **Module**: `src/smt.zig`
- **Surface rule**: `[by tautology ref1 ... refN]` (refs are premise steps or
  statements; the goal must follow propositionally)
- **Verdict semantics**: atoms are the maximal subformulas that are not
  `and`/`or`/`not`/`->` (predicates, equations, quantified formulas — all
  opaque). `.valid` means premises AND not(goal) has no truth assignment over
  those atoms. Failures are located errors, never accelerated: a satisfiable
  skeleton reports its countermodel; more than 16 distinct atoms reports the
  cap.
- **Certificate status**: certificate-first (B2). Every valid goal within
  the step budget replays as ordinary kernel steps — an inline excluded
  middle plus or_elim per split atom, structural derivation at the leaves —
  so typical uses stay kernel-checked and check green by default. The accelerated
  verdict is admitted only under `--fast` as the over-budget fallback, marking
  that use accelerated only.

### `arithmetic` — linear (Presburger) arithmetic over Nat

- **Module**: `src/presburger.zig` (decision), `src/farkas.zig` (refutation
  search for the Farkas link)
- **Surface rule**: `[by arithmetic ref1 ... refN]`, or
  `[by arithmetic(<theory>) ref...]` naming a theory module. Refs are premise
  steps or statements. **Theory resolution**: bare `arithmetic` resolves the
  vocabulary + certificate lemmas by well-known name in **local scope** (the
  self-contained case). `arithmetic(<theory>)` resolves them against an
  imported module's scope regardless of local aliases — so a downstream or
  subdomain file elaborates without dragging the arithmetic vocabulary into its
  namespace. A **named** theory must provide every symbol the goal uses (a gap
  is a hard error naming it); a missing certificate *lemma* makes the relevant
  certifier decline (soft), surfaced at the terminal.
- **Fallback**: `[by arithmetic ... fallback(<thm>)]` names a manually-proven
  theorem to cite when the certifier chain declines a valid goal — instead of
  the hard error (default) or the accelerated verdict (`--fast`). The kernel
  checks `<thm>`'s statement α-matches the goal, so the step stays
  **kernel-checked** (not accelerated), and any accelerated-tactic names `<thm>`
  itself carries are inherited. This is for goals the Presburger procedure
  *decides* but no certifier can *emit* — e.g. multi-fixed-variable `∀∀∃`
  (`tests/cases/cooper_gap.bpa`: `sumParity` reduces to the cooper-certified
  single-variable `evenOrOddArith` via a hand proof, and `fallback` cites it).
  `fallback` is a contextual modifier on `arithmetic` only (not a keyword —
  `fallback` is an ordinary identifier elsewhere); it is the
  decision-vs-certification escape hatch for a decision-backed procedure, so
  the structural presumers (`assoc`/`assoc_commut`) will never carry it.
- **Fragment**: terms over `ZERO`, `ONE`, `succ`, `add`, and `mul` where one
  side folds to a literal — all resolved by those well-known names in the
  theory scope; atoms `=`, `!=`, and `less_than`; the propositional
  connectives; `forall`/`exists` over Nat. Anything else — foreign
  predicates, nonlinear terms, quantified subformulas that are not wholly
  arithmetic — is an **opaque propositional atom** in an SMT combination
  (DPLL over the mixed skeleton in `src/smt.zig`, with the Presburger
  engine as the theory solver; refuted skeleton models are skipped).
  Opaque atoms are never instantiated: a goal needing a quantified opaque
  subformula's internals simply reports a countermodel naming it.
- **Verdict semantics**: Nat is modeled as the nonnegative integers (every
  variable carries an implicit `>= 0`). `.valid` means premises AND
  not(goal) is unsatisfiable, decided by Cooper's quantifier elimination
  (complete for Presburger arithmetic; divisibility atoms handle the
  periodicity, i128 arithmetic is overflow-checked, and elimination blowup
  hits an explicit work budget — both are honest errors). A satisfiable
  negation reports countermodel values for the fixed variables when a small
  witness exists.
- **Certificate status**: certificate-first (C2a–C2c, premise handling,
  D2). Goals replay as kernel steps when the well-known peano lemmas
  resolve in the use site's scope: ground and universally-quantified
  linear *equations* normalize to succ-towers over sorted sums (recursion
  axioms plus `addZeroRight`/`addSuccRight`/`mulZeroRight`/`mulSuccRight`/
  `addIsAssociative`; the residual permutation is a chain of
  `addIsCommutative`/`addLeftSwap` rewrites); *order* goals synthesize the
  difference witness d, certify `add(a, succ(d)) = b`, and close with a
  `lessThanIntro` instance; *existentials* search a constant witness tower
  and reduce via `exists_intro`. *Hypotheses* (cited `less_than`/`=`
  steps) enter by witness substitution: each order premise is
  `lessThanElim`-unpacked and its flipped witness equation becomes a
  ground rewrite rule, so difference-logic chains (including transitivity)
  certify; the conclusion exports back through `exists_elim`. *Mixed
  skeletons* (D2) replay as tautology-style case splits whose boolean dead
  ends close by deriving the conflicting arithmetic literal from the
  branch's assumptions, then `absurd`. *Farkas* (`src/farkas.zig`) certifies
  difference-logic constraint combinations — combining SEVERAL hypotheses,
  which the single-atom order cert cannot: an infeasible cycle `x < ... < x`
  (folded with `lessThanTransitive`), order composition (`a<b -> b<c -> a<c`, a
  path fold), an arbitrary/`false`-shaped conclusion (fold a cycle, contradict
  with `lessThanIrreflexive`, `absurd`), COEFFICIENT SCALING (`mul`-by-literal
  bounds scaled via `multiplicationPreservesOrder`), and SUMS of distinct-
  variable bounds (`a<b ∧ c<d -> add(a,c)<add(b,d)`, via
  `additionPreservesOrder` + `addIsCommutative` + transitivity). *Cooper-replay*
  (the `cooper` link, `src/presburger.zig` trace + `src/elaborate.zig`
  `cooperInduction`) closes the **quantifier-alternation tail**: a
  `forall x…; exists y; body` goal replays its Cooper elimination as
  kernel steps — for a period-1 trace, a boundary witness under an `or_intro`;
  for a period-D trace (e.g. the parity `evenOrOdd`, `forall x; exists y; x=2y ∨
  x=2y+1`), a SYNTHESIZED induction on the fixed variable (predicate `P(k)` =
  the body, base `P(ZERO)`, step `P(k)→P(succ(k))` by unpacking the IH witness
  and shifting it per residue-class arm, then `instantiate induction`). Still
  accelerated when it cannot elaborate, honestly disclosed: quantified
  arithmetic subformulas used as skeleton atoms, and multi-variable / nested
  (`∀∃∀`) alternation (the cooper link declines these, so they fall to
  `--fast`).

### `polynomial` — nonlinear ring identities

- **Module**: `src/elaborate.zig` (`polynomialEquation` / `polyCanon` for the
  kernel-checked path; `polyNormForm` for the accelerated path)
- **Surface rule**: `[by polynomial(<theory>)]` / `[by
  polynomial_quantified(<theory>)]`. Theory-parameterized exactly like
  `arithmetic` (bare = local scope; `(theory)` = that imported module).
- **Elaborated path is the DEFAULT and is NOT accelerated.** Under the default,
  `polynomial` canonicalizes both sides to a sorted sum of sorted monomials by
  *resolving the theory's ring lemmas* (`mulAddDistrib*`, `mulIsAssociative`,
  `mulLeftSwap`, one/zero folds) and emitting a rewrite chain that CITES them —
  every step kernel-rechecked. Sound relative to the theory's proofs;
  kernel-checked; not accelerated. A theory too thin (lemmas absent) is a located
  decline, not an acceleration.
- **Accelerated verdict (only under `--fast`)**: skip the lemmas entirely and
  compare the *bare syntactic semiring normal forms* (`polyNormForm` —
  flatten/sort add/mul trees assuming commutativity, associativity,
  distributivity, 0/1 identities). `.valid` = the two normal forms are
  `alphaEq`. A false identity is still REJECTED (the procedure decides). What
  is accelerated (not kernel-checked) is the **presumption that `add`/`mul` form a
  commutative semiring** — the theory's own laws are never checked, so a
  pathological/wrong `add`/`mul` could make the presumed identity false.
  Accelerated-tactic name: `polynomial`.
- **Why an accelerated tactic at all**: it decides on theories too thin to
  kernel-check, and it trusts the ring structure of symbols it does not control —
  the honest, accelerated counterpart to the default's kernel-discharged trust.
- **No `fallback` (settled — don't relitigate).** Unlike `arithmetic` (whose
  Cooper decision genuinely exceeds what the certifier can emit — the ∀∀∃ /
  nested-alternation tail — so `fallback` bridges a real gap), `polynomial`'s
  kernel-checked path and accelerated path decide the *same* fragment: semiring
  identities over `add`/`mul`. **When the ring lemmas are present, the
  kernel-checked path always succeeds** on a true identity (terminating
  normalization, every rewrite cites a present lemma) — stress-tested to a
  wide-sum 4th power (256 monomials), 100-factor reversed products,
  `succ`-atoms, and 0/1 folds. The only case the accelerated path "wins" is a
  **thin theory** (`needs <lemma> in scope`), whose fix is to *add the lemma*,
  not to hand-prove around it. So there is no decision-vs-certification gap for
  `polynomial` to bridge, and it carries no `fallback`. (The audit also
  surfaced — and fixed — a stale-slice OOB crash in the accelerated normalizer
  on large expansions: `tests/cases/polynomial_oob.bpa`.)

### `assoc_commut` — associative-commutative reordering

- **Module**: `src/elaborate.zig` (`acEquation`)
- **Surface rule**: bare `[by assoc_commut]` / `[by assoc_commut_quantified]`
  (well-known `add`/`mul` triple), or the explicit form `[by
  assoc_commut(assoc, comm, swap)]` supplying the AC lemmas for a **custom
  operator** (operator recovered from the commutativity lemma's shape). Trailing
  refs are distributivity/pre-normalization lemmas. Exactly 0 or 3 args.
- **Kernel-checked path is the DEFAULT and is NOT accelerated.** Re-associate +
  bubble-sort by the operator's assoc/comm/swap lemmas, emitting kernel-checked
  swaps that cite them. The **explicit-triple form ALWAYS emits kernel steps** (the
  triple is checkable) — it has no accelerated path.
- **Accelerated verdict (only under `--fast`, bare form only)**: compare sorted
  multisets of summands structurally, resolving NO assoc/comm/swap lemma.
  `.valid` = same sorted multiset. A different multiset is still rejected. What
  is accelerated (not kernel-checked) is the **presumption that the operator is
  associative-commutative** — never checked, so an operator that is not
  (subtraction, function composition, matrix mul, …) could make the presumed
  reordering false. Accelerated-tactic name: `assoc_commut`.
- **Relation to `polynomial`**: `assoc_commut` is the single-operator special
  case; `polynomial` additionally distributes `mul` over `add`. Same trust
  story — both presume the vocabulary's algebra where the kernel-checked path
  proves it.

### `assoc` — associativity-only reordering

- **Module**: `src/elaborate.zig` (`assocEquation`)
- **Surface rule**: `[by assoc(assocLemma)]` / `[by assoc_quantified(assocLemma)]`.
  The associativity lemma is **REQUIRED** (exactly one arg — no bare form, no
  `add`/`mul` assumption); the operator is recovered from the lemma's shape
  `f(f(a,b),c) = f(a,f(b,c))`. The non-commutative sibling of `assoc_commut`
  (for group theory etc.), where reordering is forbidden — only re-nesting.
- **Kernel-checked path is the DEFAULT and is NOT accelerated.** Right-nest each
  side by the cited associativity rule (confluent + terminating → canonical
  form), `alphaEq`-compare, and emit a kernel-checked rewrite chain that cites
  the lemma. Sides that differ by more than associativity are a located error.
- **Accelerated verdict (only under `--fast`)**: structurally right-nest both
  sides over the operator and compare, WITHOUT emitting/kernel-checking the
  rewrite chain. A shape that isn't associativity-equal is still rejected. What
  is accelerated (not kernel-checked) is the **presumption that the operator is
  associative** — the rewrite is not discharged against the kernel.
  Accelerated-tactic name: `assoc`. (Unlike `assoc_commut`, the lemma is always
  resolved even in the accelerated path, since it's required to identify the
  operator; the acceleration is for the *undischarged rewrite*, not for an
  unresolved lemma.)
