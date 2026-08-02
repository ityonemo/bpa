# The Integers

A literate `bpa` transliteration of **Chapter 2 ("The Integers")** of Thomas W.
Judson's *Abstract Algebra* (source: `vendor/aata/src/integers.xml`; © 1997–2026
Judson, GFDL 1.3). Chapter 2 develops the integers ℤ: mathematical induction,
the division algorithm, the Euclidean algorithm and Bézout's identity, and the
Fundamental Theorem of Arithmetic. Run `bpa check aata/2-integers.md`.

The integers are the axiomatic theory `std/integer.bpa` (a successor *and* a
predecessor, bidirectional induction) with its ring algebra
(`std/integer-ring.bpa`), order/subtraction (`std/integer-order.bpa`),
divisibility and powers (`std/integer-divides.bpa`), and — for ℕ-indexed
statements — the nonnegative integers with upward-from-0 induction
(`std/integer-nonneg.bpa`).

```bpa
import integer <<< "std/integer.bpa"
import ring <<< "std/integer-ring.bpa"
import order <<< "std/integer-order.bpa"
import divides <<< "std/integer-divides.bpa"
import nonneg <<< "std/integer-nonneg.bpa"

sort Int = integer.Int
const ZERO = integer.ZERO
const ONE = integer.ONE
func succ = integer.succ
func add = integer.add
func mul = integer.mul
func neg = integer.neg
func sub = order.sub
func pow = divides.pow
pred is_nonneg = nonneg.nonneg
pred does_divide = divides.divides
axiom addZeroRight = integer.addZeroRight
axiom mulZeroRight = integer.mulZeroRight
axiom mulSuccRight = integer.mulSuccRight
axiom powZero = divides.powZero
axiom powSucc = divides.powSucc
axiom dividesIntro = divides.dividesIntro
axiom dividesElim = divides.dividesElim
axiom subDef = order.subDef
axiom nonnegInduction = nonneg.nonnegInduction
theorem addZeroLeft = ring.addZeroLeft
theorem addIsCommutative = ring.addIsCommutative
theorem addIsAssociative = ring.addIsAssociative
theorem mulOneRight = ring.mulOneRight
theorem subSelf = order.subSelf

define TWO = succ(ONE)
define THREE = succ(TWO)
define FOUR = succ(THREE)
```

## Mathematical Induction

> **First Principle of Mathematical Induction.** Let $S(n)$ be a statement about
> integers for $n \in \mathbb N$ and suppose $S(n_0)$ is true for some integer
> $n_0$. If for all integers $k \ge n_0$, $S(k)$ implies $S(k+1)$, then $S(n)$ is
> true for all integers $n \ge n_0$.

In `bpa` this principle *is* an axiom of the theory: `std/integer.bpa` has a
bidirectional induction schema over all of ℤ, and `std/integer-nonneg.bpa`
carves out the nonnegatives $\mathbb N$ with the upward-from-0 principle
`nonnegInduction` — prove $P(0)$ and that $P(k) \Rightarrow P(\operatorname{succ}
k)$ for nonnegative $k$, and $P$ holds on all of $\mathbb N$. That is the first
principle at $n_0 = 0$, which (after a shift) is all the examples use.

The book illustrates induction with divisibility facts such as "$9$ divides
$10^{n+1} + 3\cdot 10^n + 5$." We prove one of the same flavour, whose induction
starts cleanly at $0$: **$3$ divides $4^n - 1$** for every $n \ge 0$ (equivalently
$4^n \equiv 1 \pmod 3$).

At $n = 0$: $4^0 - 1 = 1 - 1 = 0$, and $3 \mid 0$.

```bpa
theorem baseCase: does_divide(THREE, sub(pow(FOUR, ZERO), ONE))
proof
  @four-to-zero-rule |
    forall b: Int; pow(b, ZERO) = ONE
    [by axiom powZero]
  @four-to-zero |
    pow(FOUR, ZERO) = ONE
    [by forall_elim(FOUR) four-to-zero-rule]
  @reflexivity-of-difference |
    sub(pow(FOUR, ZERO), ONE) = sub(pow(FOUR, ZERO), ONE)
    [by reflexivity]
  @difference-of-ones |
    sub(pow(FOUR, ZERO), ONE) = sub(ONE, ONE)
    [by rewrite four-to-zero reflexivity-of-difference]
  @sub-self-rule |
    forall a: Int; sub(a, a) = ZERO
    [by theorem subSelf]
  @one-minus-one |
    sub(ONE, ONE) = ZERO
    [by forall_elim(ONE) sub-self-rule]
  @difference-is-zero |
    sub(pow(FOUR, ZERO), ONE) = ZERO
    [by rewrite one-minus-one difference-of-ones]
  @mul-zero-rule |
    forall n: Int; mul(n, ZERO) = ZERO
    [by axiom mulZeroRight]
  @three-times-zero |
    mul(THREE, ZERO) = ZERO
    [by forall_elim(THREE) mul-zero-rule]
  @zero-as-product |
    ZERO = mul(THREE, ZERO)
    [by symmetry three-times-zero]
  @divides-intro |
    forall d, n, k: Int; n = mul(d, k) -> does_divide(d, n)
    [by axiom dividesIntro]
  @intro-at-zero |
    ZERO = mul(THREE, ZERO) -> does_divide(THREE, ZERO)
    [by forall_elim(THREE, ZERO, ZERO) divides-intro]
  @three-divides-zero |
    does_divide(THREE, ZERO)
    [by modus_ponens intro-at-zero zero-as-product]
  @zero-as-difference |
    ZERO = sub(pow(FOUR, ZERO), ONE)
    [by symmetry difference-is-zero]
  @conclusion |
    does_divide(THREE, sub(pow(FOUR, ZERO), ONE))
    [by rewrite zero-as-difference three-divides-zero]
qed
```

The inductive step and the full ∀n≥0 statement follow. (Proof to fill: from
$3 \mid 4^k - 1$, write $4^{k+1} - 1 = 4\cdot 4^k - 1 = 4(4^k - 1) + 3$; both
$4(4^k-1)$ and $3$ are divisible by 3, so their sum is.)

```bpa
  hole fourthPowerMinusOne:
  forall n: Int; is_nonneg(n) -> does_divide(THREE, sub(pow(FOUR, n), ONE))
```
