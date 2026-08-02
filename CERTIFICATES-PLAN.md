# Certificates plan — kernel-checked-by-default, fast-mode-for-development

## STATUS (2026-07-30): the mode inversion has LANDED, further than this doc anticipated

Implemented: verification is now modeled as independent knobs
(`Verify { certify_arithmetic, recheck_imports, recheck_schemas }`,
src/elaborate.zig) with the CLI presets `--fast` / `--faster` / `--reckless`
turning off one layer each. **`--pure` and `--recursive` are removed** —
full verification (all knobs on) is the default, and there is **no
accelerated fallback in default mode**: a `by arithmetic` that can't
certify is a hard error pointing at `--fast`. Each speed flag prints a loud
"ACCELERATED" banner. So the sequencing below is superseded: steps 2–4
(mode spectrum) are done and collapsed into a two-real-modes design
(verified-by-default vs. `--fast`), NOT the three-mode spectrum this doc
described.

**UPDATE (2026-07-30): Farkas has LANDED** (`src/farkas.zig` + the
`farkasCertificate` link + the reason-carrying certifier chain in
`elaborate.zig`). It certifies difference-logic **infeasibility** (order-cycle
`x < ... < x` folded with `lessThanTransitive`) purely under the default. Also
landed alongside: the **theory-argument** surface (`by arithmetic(<module>)`)
resolving vocabulary + lemmas against a named upstream theory module instead of
local aliases, and the **certifier chain** (Outcome/Reason) whose terminal
lists each link's decline reason. What REMAINS is the ∀∃ tail: `examples/peano.bpa`'s
`evenOrOdd` accelerated step is **Cooper-QE, not Farkas**, so it still needs `--fast`
until Cooper-replay lands (a peer chain link). Coefficient-scaling Farkas
(`mul`-by-literal bounds) and the `false`-concluding infeasibility form
(irreflexivity + absurd cap) are the near-term Farkas extensions. The
historical plan is kept below for the Farkas/Cooper detail.

**KNOWN CERTIFIER GAP (2026-07-30): positive-conclusion linear order.** A
`by arithmetic` audit of the std corpus surfaced a shape that is **decided
valid but has no emitting link**: from a linear equation + a strict bound,
conclude a *positive* strict order, e.g.
`forall a, b, x; add(x, b) = a -> less_than(ZERO, b) -> less_than(x, a)`
(the in-fragment tail of `peano-subtraction.bpa`'s `subStrictlyDecreases`,
with `sub(a,b)` read as an opaque `x`). Presburger says VALID, but the chain
declines it — equation/order/exists and mixed-skeleton report `out_of_scope`,
and Farkas only handles *infeasibility* / `false` conclusions and order
*composition* (`a<b -> b<c -> a<c`), not "equation + `0<b` ⊢ `x<a`". So it
falls to the accelerated tactic under `--fast`. This is why the audit collapsed **no** std
proofs: rewriting such a hand proof as `by arithmetic` would trade a kernel-checked proof
for an accelerated one. This gap is **distinct from the Cooper-QE tail** —
it is quantifier-free and linear, so a new peer chain link (a "positive linear
order" certifier: rearrange the equation into `lessThanIntro` gap form —
`add(x, succ(d)) = a` from `add(x, b) = a` and the gap witness of `0 < b` —
then cite `lessThanIntro`) would close it with a fixed-shape emit, no search.
Lower priority than Cooper (rare in the corpus; the hand proofs are already
kernel-checked), but the cheaper of the two to build.

## The long-term goal (user-decided)

Invert the trust default so **kernel-checking is the norm and speed is opt-in**:

- **Default `by arithmetic`** produces a *full certificate* — ordinary
  kernel-checked steps. The accelerated tactic is a genuine last resort, not a
  fallback you silently drift into. A proof that ships is fully proven unless it
  truly cannot be.
- **Fast mode** (opt-in, dev-time) skips certificate generation and takes the
  accelerated verdict directly, for quick iteration while you are still finding
  out whether a proof even goes through. You *develop* in fast mode and
  *finalize* in default mode.

This matches how proofs are actually written (you don't want to pay for
certificate generation on every edit of a still-broken proof) and makes the
trustworthy thing the default rather than something to remember to ask for.

## Why this is achievable — and its exact boundary

"Turn any positive `by arithmetic` verdict into a real proof" is
**proof-producing / certifying decision procedures**. Whether it is possible
is fragment-dependent, and the boundary is sharp:

| Fragment | Certifiable? | Status |
|---|---|---|
| Ground equalities / computations | yes | done (C2a) |
| Universal linear equalities / order | yes | done (C2b) |
| Existentials, constant witness | yes | done (C2c) |
| Hypothesis chains (difference logic) | yes | done (premise-C2) |
| Propositional skeleton (`tautology`) | yes | done (B2) |
| **QF-linear infeasibility (general)** | **yes — Farkas** | **NOT done — the big lever** |
| Full quantifier alternation (Cooper QE replay) | yes in principle, hard | not done |
| Nonlinear (`mul(x, y)` both variable) | **no** — undecidable, no complete certifier exists | n/a |

Two facts fix the whole shape of the work:

- **The quantifier-free linear core always has a checkable certificate.** An
  infeasible conjunction of linear constraints has a **Farkas certificate**:
  nonnegative multipliers that combine the hypotheses into `0 ≥ 1` (or
  `0 < 0`). That combination *is* a kernel proof — a fixed recipe computed
  directly from the infeasibility, no search. This is the single highest-value
  piece: it flips the *entire* QF-linear fragment (most real `by arithmetic`
  uses) from accelerated to kernel-checked in one stroke.
- **Full quantifier-alternation replay (Cooper QE) is possible but large.**
  Cooper's algorithm is constructive — every elimination step is a logical
  equivalence with a proof — but the `∀`/`∃`-elimination proof expands to a
  big disjunction with divisibility side-conditions, so replaying it as kernel
  steps is deep, careful work. This is the honest candidate to *stay*
  accelerated for a while; the accelerated/`--pure` disclosure exists precisely
  for it.
- **Nonlinear cannot be fully certified at all** (undecidability). Only
  incomplete certifiers exist (Gröbner for equalities, SOS for inequalities);
  see `NONLINEAR-PLAN.md`.

## The three-mode spectrum

The current `Elaborator.pure: bool` (src/elaborate.zig:49, set from `--pure`)
generalizes to a mode enum. The seam already exists: `arithmeticJustification`
(src/elaborate.zig ~2565) is already *certificate-first, accelerated-fallback per
use* — this reorders and gates that logic on the mode.

- **`--pure`** — certificate or a located error. Never accelerated. (Exists
  today.) The strict end: a passing proof has provably zero unchecked steps.
- **default** — certificate-preferred. Attempt the certificate; the behavior
  when it can't certify is the staged decision below.
- **`--fast`** (or `--draft`) — acceleration-preferred. Skip certificate
  generation, take the verdict. Dev-time only. **Loud, never silent:** the
  summary reads e.g. `OK: 21 theorems (FAST MODE — accelerated verdicts
  unverified; re-run without --fast before finalizing)`. Consistent with the
  existing disclosure philosophy — fast mode is ergonomic but always
  announced.

`--pure` and `--fast` are the two ends; default sits between. `--pure` and
`--fast` are mutually exclusive (error if both given).

## Default-mode behavior: staged cutover

The subtlety: certificate generation is not yet possible for the whole
fragment (Cooper QE replay isn't built). So "default = full proof" must
answer *what happens when the default cannot certify.* Two behaviors, adopted
in sequence:

- **(b) certificate-preferred, accelerated fallback** — default tries the
  certificate, falls back to the accelerated tactic *with the existing
  disclosure + summary line*. Nothing hard-fails. This is essentially today's
  behavior with the priority made explicit. **Use during build-out.**
- **(a) certificate-or-error for the covered fragment** — once the certifier
  covers enough, a goal *in the certifiable fragment* that somehow fails to
  certify is an error, and only the genuinely-hard tail (Cooper QE) falls
  back to an accelerated step. This is what makes "the default is a real proof"
  a **guarantee** for the covered fragment, not a hope. **Cut over to this
  when Farkas + the common cases make hard-failing tolerable.**

Target end-state: default mode fully proves everything except the
quantifier-alternation tail, that tail is accelerated-and-disclosed, and `--pure`
rejects even the tail. `--fast` bypasses all of it for development.

## Sequencing

The mode machinery is easy; the gating work is **certifier coverage**, so
coverage comes first.

1. **Farkas certificate for QF-linear arithmetic** — the biggest single
   coverage jump. `src/presburger.zig` already computes the infeasibility;
   the missing piece is *recording the refutation multipliers* during the
   decision and emitting the combination proof (`multiplicationPreservesOrder`
   + `additionPreservesOrder` + `absurd` over the cited hypotheses — a
   fixed-shape emit, no search). Turns most `by arithmetic` uses kernel-checked. RED
   fixture: an inequality-infeasibility goal that currently falls to the
   accelerated tactic, proven with every step kernel-checked under `--pure` after.
2. **Mode spectrum** — `Elaborator.pure: bool` → a `Mode` enum
   (`pure` / `default` / `fast`); `--fast` flag in src/main.zig + src/root.zig
   (mirror the `--pure` plumbing); loud fast-mode summary line; `--pure` +
   `--fast` mutually-exclusive error. Small, mostly plumbing.
3. **Default = behavior (b)** — reorder `arithmeticJustification` so default
   is certificate-preferred with accelerated fallback (explicit, not incidental).
4. **Cut default to behavior (a)** for the covered fragment once coverage is
   wide enough to hard-fail without being infuriating.
5. **Cooper QE replay** (long pole, optional/eventual) — closes the last gap
   so quantifier-alternation goals certify too; until then the disclosure
   keeps the tail honest.

Each step is RED-first (integration `.bpa` fixture + `build.zig` golden with
`has_side_effects`, exact stdout/stderr, `--pure`/`--fast` gates) per the
fractal-TDD directive, with unit tests in the touched module.

## Verification

- `zig build test` — existing goldens green + new gates.
- After step 1: the QF-linear infeasibility fixtures pass under `--pure`
  (previously accelerated-only).
- Fast mode: a goal outside the certified fragment passes under `--fast` with
  the loud summary; the same goal under `--pure` is a located error; under
  default it behaves per the current stage (b→a).
- The `--pure`/`--fast` mutual-exclusion error is gated.

## Relationship to the other plans

- `NONLINEAR-PLAN.md` — the `polynomial` identity tactic and `div`/`mod` are
  *kernel-checked from the start* (equational), so they never become accelerated at
  all; they shrink what `arithmetic` is even asked to do.
- This plan is about the *linear* accelerated tactic: making its verdicts
  certify by default, with Farkas as the lever and Cooper QE as the honest
  remaining tail. The nonlinear fragment stays permanently partial (undecidable)
  and is out of scope here.
