# EXT-PLAN.md — the `ext` accelerated tactic (extensionality-reduction)

## 0. Goal and principle

`ext(<theory>)` is an **accelerated tactic** (ACCELERATION.md family) that proves
an equation `LHS = RHS` between two *extensional* objects by reducing it, via the
theory's **extensionality lemma**, to a pointwise obligation, then discharging
that obligation by unfolding the operators (via the theory's *characterization
lemmas*) and closing the residue.

It is a **structure tactic, parameterized by model** — exactly like
`polynomial(peano)` / `arithmetic(theory)`. The structure is *extensionality*;
the model is whatever theory you name. It is NOT set-theory-specific: the SAME
tactic proves set equations (`ext(set)`) and function equations (`ext(function)`),
and any future extensional theory for free. Prior art: Lean's `ext`.

Collapses the ~50-85-line hand proofs in `aata/1.2.1-sets.md` /
`aata/1.2.2-functions.md` to one line each, matching the textbook's element-chase
argument (`x ∈ LHS ⟺ x ∈ RHS`).

## 1. The two model instances (verified against the code)

**Sets** (`std/set.bpa`): element sort `Universe`, characterization predicate
`member(x, s)`. Extensionality:
```
axiom extensionality: forall a, b: Set;
  (forall x: Universe; member(x, a) -> member(x, b)) ->
  (forall x: Universe; member(x, b) -> member(x, a)) -> a = b
```
— TWO subset directions (no `<->` in bpa). Operator characterization lemmas
(each an `and` of two `->`): `unionMember`, `intersectionMember`,
`differenceMember`, `complementMember`, `emptysetMember`. The pointwise residue
after unfolding is PROPOSITIONAL over atoms `member(x, <basic set>)` → closed by
**`tautology`**.

**Functions** (`std/function.bpa`): element sort `Universe`, characterization
FUNCTION `apply(f, x)`. Extensionality:
```
axiom funcExtensionality: forall f, g: Fn;
  (forall x: Universe; apply(f, x) = apply(g, x)) -> f = g
```
— a SINGLE direction (equality is symmetric). Operator characterization lemmas:
`composeApply` (`apply(compose(g,f),x) = apply(g, apply(f,x))`), `identityApply`
(`apply(identityFn,x) = x`). The pointwise residue is an EQUATION
`apply(LHS,x) = apply(RHS,x)` → closed by the **equation certifier**
(`arithCertCore`/`planInner` — reused).

**The two axes that vary between models**, both READ OFF the extensionality
lemma's shape (so ONE tactic handles both):
| | sets | functions |
|---|---|---|
| obligation count | 2 (`A⊆B`, `B⊆A`) | 1 (pointwise `=`) |
| characterization | predicate `member` | function `apply` |
| pointwise residue | propositional | equational |
| closer | `tautology` | equation certifier |

## 2. Surface syntax + dispatch

- **Rule name**: `ext`, quantified variant `ext_quantified` (mirrors
  `polynomial`/`polynomial_quantified`). A bare `LHS = RHS` goal uses `ext`; a
  `forall …; LHS = RHS` goal uses `ext_quantified` (peels the prefix first).
- **Theory arg**: `ext(set)` / `ext(function)` — theory-parameterized exactly
  like `arithmetic(theory)`: sets `self.theory_file` for the resolution scope.
  Register `ext`/`ext_quantified` in `isTheoryRule` (parser) so the `(theory)`
  paren is accepted.
- Add `ext`, `ext_quantified` to the `RuleKind` enum (elaborate.zig:843) and the
  `rule_names` map (:849), and dispatch arms in `lowerJustification` (:1053+)
  → `extJustification` / `extQuantifiedJustification`.

## 3. Symbol resolution (`ExtSymbols`)

Resolve against `self.theoryScope()` (theory arg or local), mirroring
`presburger.Symbols` + `wellKnownSym`/`wellKnownFact`:
```
ExtSymbols {
    universe: SortId,           // well-known sort "Universe"
    ext_lemma: TermId+source,   // "extensionality" (fallback "funcExtensionality")
    // the characterization symbol is DISCOVERED from the goal, not fixed:
    //   the ext lemma's obligation mentions `member(x,a)` / `apply(f,x)` — read
    //   the predicate/func head from the lemma's premise to know how to unfold.
}
```
The **operator characterization lemmas** are NOT a fixed list — resolve them by
walking the goal: for each operator subterm `op(...)` appearing in LHS/RHS (e.g.
`union`, `intersection`, `compose`, `identityFn`), look up its characterization
lemma by the well-known name `<op>Member` (sets) / `<op>Apply` (functions), OR —
more robustly — resolve ALL characterization lemmas the theory exports whose
statement has the shape `forall …; forall x:Universe; <char>(x, op(...)) <iff> …`
and keep the ones whose operator appears in the goal. Decline (`missing_lemma`)
if an operator in the goal has no characterization lemma in scope.

Resolution of the ext lemma itself: try `extensionality`, then
`funcExtensionality` (or: any theory axiom of shape
`forall A,B; (obligations) -> A = B` whose `A=B` conclusion sort-matches the
goal's sides). Decline `out_of_scope` if none.

## 4. The emit (elaborated / kernel-checked path)

For a bare goal `LHS = RHS` (the `_quantified` variant first peels the `forall`
prefix into fix blocks via `peelUniversal`, like the other tactics):

1. **Instantiate the ext lemma** at (LHS, RHS): `forall_elim(LHS, RHS) ext-lemma`
   → an implication chain `Ob1 -> (Ob2 ->) LHS = RHS` where each `Obi` is a
   `forall x:Universe; <pointwise>`.
2. **For each obligation `Obi = forall x:Universe; body_i`:**
   - `fix x: Universe` (newBlock `.fix`).
   - Instantiate every relevant operator characterization lemma at the goal's
     sets/functions and at `x` (`forall_elim(<args>) <lemma>` then
     `forall_elim(x)`), producing the unfolded membership/apply facts as steps.
   - Emit the residue proof:
     - **predicate model (sets):** the body is `member(x,LHS) -> member(x,RHS)`;
       close by `tautology` citing the unfolded biconditional steps + any
       hypothesis. (Exactly the existing hand-proof leaf — see
       `unionCommutative` in aata/1.2.1-sets.md.)
     - **function model:** the body is `apply(LHS,x) = apply(RHS,x)`; close by
       `arithCertCore`/the equation certifier citing the `composeApply`/
       `identityApply` unfoldings as rewrite premises. (Exactly the funcExt
       rewrite chain in aata/1.2.2-functions.md's `composeAssoc`.)
   - `forall_intro` to rebuild `Obi`, giving a step proving `Obi`.
3. **Chain the obligations into `LHS = RHS`:** `modus_ponens` the instantiated
   ext lemma against each `Obi` step in order (2 for sets, 1 for functions).
4. **_quantified**: fold back out through the peeled fix blocks (`forall_intro`).

All steps are kernel tactics (`forall_elim`/`forall_intro`/`modus_ponens`/`fix`/
`tautology`-emitted-chain/rewrite) — so `ext` EMITS (kernel-checked) by default.
The accelerated (`--fast`) path may presume the reduction; but note the residue
closer is itself `tautology`/equation-cert, which emit — so `ext` is expected to
be an accelerated tactic that essentially always emits (like `simplify`/
`polynomial`), rarely needing `--fast`.

## 5. Decline reasons (accelerated-tactic contract)

- goal not an equation (or `forall…; eq` for `_quantified`) → `out_of_scope`.
- no extensionality lemma in scope whose conclusion matches the goal sort →
  `.{ .missing_lemma = "extensionality" }`.
- `Universe` sort not resolvable → `.{ .missing_symbol = "Universe" }`.
- an operator in the goal has no characterization lemma → `.{ .missing_lemma =
  "<op>Member" }` (actionable: name the lemma to add).
- residue not closable (tautology countermodel / equation cert declines) → the
  goal is likely FALSE; report the closer's own diagnostic.

## 6. Tests (RED-first, BOTH domains — user requirement)

Two self-contained `.bpa` fixtures + integration goldens, and unit coverage:

- **`tests/cases/ext_set.bpa`** — imports `std/set.bpa`, proves a couple of set
  identities with `[by ext_quantified(set)]` that today need ~85 lines by hand:
  - `intersectionCommutative: forall a, b: Set; intersection(a,b) = intersection(b,a)`
  - `unionAssociative: forall a, b, c: Set; union(union(a,b),c) = union(a,union(b,c))`
  Checks kernel-checked (default mode, no --fast). RED: falls to the terminal
  before `ext` exists; GREEN after.
- **`tests/cases/ext_function.bpa`** — imports `std/function.bpa`, proves a
  function identity with `[by ext_quantified(function)]`:
  - `composeAssoc: forall h, g, f: Fn; compose(compose(h,g),f) = compose(h,compose(g,f))`
  Checks kernel-checked in default mode.
- **Integration goldens** in `tests/test_tactics.zig`: both fixtures `ctx.ok`
  with their exact `OK: N declarations, M theorems proven` lines; a `_bad`
  fixture (a FALSE set "identity") asserting the tautology-countermodel decline;
  a thin-theory fixture (ext lemma absent) asserting the `missing_lemma` decline.
- **AATA payoff (separate follow-up, not blocking)**: rewrite the verbose
  hand proofs in `aata/1.2.1-sets.md` / `aata/1.2.2-functions.md` to `[by ext…]`
  one-liners; the declaration/theorem counts stay, the files shrink drastically,
  and `query accelerated` will now flag those steps (correctly — `ext` is an
  accelerated tactic). Update the aata check goldens for the new counts.
- **ACCELERATION.md**: register `ext` (module, surface rule, both model shapes,
  elaborated/accelerated split, decline reasons).

## 7. Sequencing

1. Enum + rule_names + dispatch + parser `isTheoryRule` (plumbing).
2. `ExtSymbols` resolution (Universe, ext lemma, operator lemmas by goal walk).
3. `extJustification` for the **set** (predicate/tautology) model + `ext_set.bpa`
   RED→GREEN.
4. Extend to the **function** (equation) model + `ext_function.bpa` RED→GREEN
   (shares the skeleton; only the residue closer + obligation count differ).
5. `_quantified` prefix peeling (both fixtures use it).
6. Decline-path fixtures + ACCELERATION.md + goldens.
7. (Follow-up) collapse the aata hand proofs to `[by ext…]`.

## 8. NON-goals
- No `<->` connective work — obligations stay `and`-of-`->` (sets) / single `=`
  (functions), read off the lemma.
- No choice/quotient machinery — `ext` only proves EQUATIONS between existing
  objects, never constructs one (so §1.2.2 backward / §1.2.3 stay deferred).
- Not hardcoded per-domain — ONE `ext`, model via the theory arg.
