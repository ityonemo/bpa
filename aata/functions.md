# Functions

A literate `bpa` transliteration of **Chapter 1 ("Preliminaries"), §1.2.2
"Cartesian Products and Mappings"** of Thomas W. Judson's *Abstract Algebra:
Theory and Applications* (source: `vendor/aata/src/sets.xml`; © 1997–2026
Judson, GFDL 1.3). The book's prose is reproduced in order; each result the book
states is followed by a machine-checked `bpa` proof. Run
`bpa check aata/functions.md` to verify every proof block below.

The theory of mappings lives in `std/function.bpa`: functions are opaque `Fn`
objects over a fixed element domain `Universe`, with `apply`, `compose`, an
identity map, and the `injective` / `surjective` / `invertible` properties,
fixed by their defining axioms plus **function extensionality** (maps agreeing
at every point are equal). We import it and keep the library names, aliasing
only `identityFn` to the book's `id`.

```bpa
import function <<< "std/function.bpa"

sort Universe = function.Universe
sort Fn = function.Fn
const id = function.identityFn
func apply = function.apply
func compose = function.compose
pred injective = function.injective
pred surjective = function.surjective
pred invertible = function.invertible
axiom composeApply = function.composeApply
axiom identityApply = function.identityApply
axiom funcExt = function.funcExtensionality
axiom injectiveDef = function.injectiveDef
axiom surjectiveDef = function.surjectiveDef
axiom invertibleDef = function.invertibleDef
```

> *Modeling note. `std/function.bpa` models every map as `f : Universe ->
> Universe` — a single element domain, which is all the results below need. So
> the book's **Cartesian product** `A × B` (ordered pairs) and its account of a
> function as a set of pairs `f ⊂ A × B` are not encoded: they would need a
> `Universe × Universe` pair sort and a set-of-pairs theory this file does not
> build. `bpa` instead takes `apply(f, x)` as primitive — the same `f(x) = b`,
> without the underlying pair set — and fixes a function by what `apply` does to
> it. The prose below is reproduced in full; where it depends on pairs (the
> product examples, "well-defined") it is exposition, not a formal claim.*

## Cartesian Products and Mappings

Given sets $A$ and $B$, we can define a new set $A \times B$, called the **Cartesian product** of $A$ and $B$, as a set of ordered pairs. That is,

$$A \times B = \{ (a,b) : a \in A \text{ and } b \in B \}$$.

**Example.** If $A = \{ x, y \}$, $B = \{ 1, 2, 3 \}$, and $C = \emptyset$, then $A \times B$ is the set

$$\{ (x, 1), (x, 2), (x, 3), (y, 1), (y, 2), (y, 3) \}$$

and

$$A \times C = \emptyset$$.

We define the **Cartesian product of $n$ sets** to be

$$A_1 \times \cdots \times A_n = \{ (a_1, \ldots, a_n): a_i \in A_i \text{ for } i = 1, \ldots, n \}$$.

If $A = A_1 = A_2 = \cdots = A_n$, we often write $A^n$ for $A \times \cdots \times A$ (where $A$ would be written $n$ times). For example, the set ${\mathbb R}^3$ consists of all of 3-tuples of real numbers.

Subsets of $A \times B$ are called **relations**. We will define a **mapping** or **function** $f \subset A \times B$ from a set $A$ to a set $B$ to be the special type of relation where each element $a \in A$ has a unique element $b \in B$ such that $(a, b) \in f$. Another way of saying this is that for every element in $A$, $f$ assigns a unique element in $B$. We usually write $f:A \rightarrow B$ or $A \stackrel{f}{\rightarrow} B$. Instead of writing down ordered pairs $(a,b) \in A \times B$, we write $f(a) = b$ or $f : a \mapsto b$. The set $A$ is called the **domain** of $f$ and

$$f(A) = \{ f(a) : a \in A \} \subset B$$

is called the **range** or **image** of $f$. We can think of the elements in the function's domain as input values and the elements in the function's range as output values.

**Example.** Suppose $A = \{1, 2, 3 \}$ and $B = \{a, b, c \}$. In the figure below we define relations $f$ and $g$ from $A$ to $B$. The relation $f$ is a mapping, but $g$ is not because $1 \in A$ is not assigned to a unique element in $B$; that is, $g(1) = a$ and $g(1) = b$.

*(Figure omitted: Mappings and relations — two sets of ovals, A and B, relating 1, 2, 3 to a, b, c. The first mapping, f, sends 1 to b and 2 and 3 to c. The second relation, g, sends 1 to a and b, 2 to c, and 3 to a.)*

Given a function $f : A \rightarrow B$, it is often possible to write a list describing what the function does to each specific element in the domain. However, not all functions can be described in this manner. For example, the function $f: {\mathbb R} \rightarrow {\mathbb R}$ that sends each real number to its cube is a mapping that must be described by writing $f(x) = x^3$ or $f:x \mapsto x^3$.

Consider the relation $f : {\mathbb Q} \rightarrow {\mathbb Z}$ given by $f(p/q) = p$. We know that $1/2 = 2/4$, but is $f(1/2) = 1$ or $2$? This relation cannot be a mapping because it is not well-defined. A relation is **well-defined** if each element in the domain is assigned to a *unique* element in the range.

If $f:A \rightarrow B$ is a map and the image of $f$ is $B$, i.e., $f(A) = B$, then $f$ is said to be **onto** or **surjective**. In other words, if there exists an $a \in A$ for each $b \in B$ such that $f(a) = b$, then $f$ is onto. A map is **one-to-one** or **injective** if $a_1 \neq a_2$ implies $f(a_1) \neq f(a_2)$. Equivalently, a function is one-to-one if $f(a_1) = f(a_2)$ implies $a_1 = a_2$. A map that is both one-to-one and onto is called **bijective**.

**Example.** Let $f:{\mathbb Z} \rightarrow {\mathbb Q}$ be defined by $f(n) = n/1$. Then $f$ is one-to-one but not onto. Define $g : {\mathbb Q} \rightarrow {\mathbb Z}$ by $g(p/q) = p$ where $p/q$ is a rational number expressed in its lowest terms with a positive denominator. The function $g$ is onto but not one-to-one.

Given two functions, we can construct a new function by using the range of the first function as the domain of the second function. Let $f : A \rightarrow B$ and $g : B \rightarrow C$ be mappings. Define a new map, the **composition** of $f$ and $g$ from $A$ to $C$, by $(g \circ f)(x) = g(f(x))$.

*(Figure omitted: Composition of maps — two sets of ovals, A and B, relating 1, 2, 3 to a, b, c and a, b, c to X, Y, Z. The first mapping, f, sends 1 to b, 2 to c, and 3 to a. The second relation, g, sends a and b to Z and c to X. The bottom map, g∘f, sends 1 and 3 to Z and 2 to X.)*

**Example.** Consider the functions $f: A \rightarrow B$ and $g: B \rightarrow C$ that are defined in the figure above (top). The composition of these functions, $g \circ f: A \rightarrow C$, is defined in the figure above (bottom).

**Example.** Let $f(x) = x^2$ and $g(x) = 2x + 5$. Then

$$(f \circ g)(x) = f(g(x)) = (2x + 5)^2 = 4x^2 + 20x + 25$$

and

$$(g \circ f)(x) = g(f(x)) = 2x^2 + 5$$.

In general, order makes a difference; that is, in most cases $f \circ g \neq g \circ f$.

**Example.** Sometimes it is the case that $f \circ g= g \circ f$. Let $f(x) = x^3$ and $g(x) = \sqrt[3]{x}$. Then

$$(f \circ g )(x) = f(g(x)) = f( \sqrt[3]{x}\, ) = (\sqrt[3]{x}\, )^3 = x$$

and

$$(g \circ f )(x) = g(f(x)) = g( x^3) = \sqrt[3]{ x^3} = x$$.

**Example.** Given a $2 \times 2$ matrix

$$A =
\begin{pmatrix}
a & b \\
c & d
\end{pmatrix}$$,

we can define a map $T_A : {\mathbb R}^2 \rightarrow {\mathbb R}^2$ by

$$T_A (x,y) = (ax + by, cx +dy)$$

for $(x,y)$ in ${\mathbb R}^2$. This is actually matrix multiplication; that is,

$$\begin{pmatrix}
a & b \\
c & d
\end{pmatrix}
\begin{pmatrix}
x \\ y
\end{pmatrix}
=
\begin{pmatrix}
ax + by \\
cx +dy
\end{pmatrix}$$.

Maps from ${\mathbb R}^n$ to ${\mathbb R}^m$ given by matrices are called **linear maps** or **linear transformations**.

**Example.** Suppose that $S = \{ 1,2,3  \}$. Define a map $\pi :S\rightarrow S$ by

$$\pi( 1 )  = 2, \qquad \pi( 2 )  = 1, \qquad \pi( 3 )  = 3$$.

This is a bijective map. An alternative way to write $\pi$ is

$$\begin{pmatrix}
1 & 2 & 3 \\
\pi(1) & \pi(2) & \pi(3)
\end{pmatrix}
=
\begin{pmatrix}
1 & 2 & 3 \\
2 & 1 & 3
\end{pmatrix}$$.

For any set $S$, a one-to-one and onto mapping $\pi : S \rightarrow S$ is called a **permutation** of $S$.

## Theorem

> Let $f : A \rightarrow B$, $g : B \rightarrow C$, and $h : C \rightarrow D$. Then
>
> 1. The composition of mappings is associative; that is, $(h \circ g) \circ f = h \circ (g \circ f)$;
> 2. If $f$ and $g$ are both one-to-one, then the mapping $g \circ f$ is one-to-one;
> 3. If $f$ and $g$ are both onto, then the mapping $g \circ f$ is onto;
> 4. If $f$ and $g$ are bijective, then so is $g \circ f$.

We formalize all four parts. **(1) associativity** is a function-extensionality
argument: the two composites agree at every point `x` after unfolding
`compose` via `composeApply`, so `funcExt` equates them.

```bpa
// Theorem A.1: composition is associative.
theorem composeAssoc: forall h, g, f: Fn;
  compose(compose(h, g), f) = compose(h, compose(g, f))
proof
  @gen-h |
    fix h: Fn {
      @gen-g |
        fix g: Fn {
          @gen-f |
            fix f: Fn {
              @pointwise |
                fix x: Universe {
                  // LHS applied at x
                  @ca |
                    forall gg, ff: Fn; forall y: Universe;
                      apply(compose(gg, ff), y) = apply(gg, apply(ff, y))
                    [by axiom composeApply]
                  @lhs1 |
                    apply(compose(compose(h, g), f), x) = apply(compose(h, g), apply(f, x))
                    [by forall_elim(compose(h, g), f, x) ca]
                  @lhs2 |
                    apply(compose(h, g), apply(f, x)) = apply(h, apply(g, apply(f, x)))
                    [by forall_elim(h, g, apply(f, x)) ca]
                  @lhs |
                    apply(compose(compose(h, g), f), x) = apply(h, apply(g, apply(f, x)))
                    [by rewrite lhs2 lhs1]
                  // RHS applied at x
                  @rhs1 |
                    apply(compose(h, compose(g, f)), x) = apply(h, apply(compose(g, f), x))
                    [by forall_elim(h, compose(g, f), x) ca]
                  @rhs2 |
                    apply(compose(g, f), x) = apply(g, apply(f, x))
                    [by forall_elim(g, f, x) ca]
                  @rhs |
                    apply(compose(h, compose(g, f)), x) = apply(h, apply(g, apply(f, x)))
                    [by rewrite rhs2 rhs1]
                  // equate the two sides at x
                  @rhs-sym |
                    apply(h, apply(g, apply(f, x))) = apply(compose(h, compose(g, f)), x)
                    [by symmetry rhs]
                  @eq-at-x |
                    apply(compose(compose(h, g), f), x) = apply(compose(h, compose(g, f)), x)
                    [by rewrite rhs-sym lhs]
                }
              @all-x |
                forall x: Universe;
                  apply(compose(compose(h, g), f), x) = apply(compose(h, compose(g, f)), x)
                [by forall_intro pointwise]
              @ext |
                forall p, q: Fn;
                  (forall x: Universe; apply(p, x) = apply(q, x)) -> p = q
                [by axiom funcExt]
              @ext-at |
                (forall x: Universe; apply(compose(compose(h, g), f), x) = apply(compose(h, compose(g, f)), x))
                  -> compose(compose(h, g), f) = compose(h, compose(g, f))
                [by forall_elim(compose(compose(h, g), f), compose(h, compose(g, f))) ext]
              @done |
                compose(compose(h, g), f) = compose(h, compose(g, f))
                [by modus_ponens ext-at all-x]
            }
          @close-f |
            forall f: Fn; compose(compose(h, g), f) = compose(h, compose(g, f))
            [by forall_intro gen-f]
        }
      @close-g |
        forall g, f: Fn; compose(compose(h, g), f) = compose(h, compose(g, f))
        [by forall_intro gen-g]
    }
  @conclusion |
    forall h, g, f: Fn; compose(compose(h, g), f) = compose(h, compose(g, f))
    [by forall_intro gen-h]
qed
```

**(2) injective ∘ injective is injective** (the book's exercise): if
`(g∘f)(a) = (g∘f)(b)` then `g(f(a)) = g(f(b))`; `g` injective gives
`f(a) = f(b)`; `f` injective gives `a = b`.

```bpa
// Theorem A.2: inj ∘ inj is injective.
// If (g∘f)(a)=(g∘f)(b) then g(f(a))=g(f(b)); g injective gives f(a)=f(b); f
// injective gives a=b.
theorem composeInjective: forall g, f: Fn;
  injective(g) -> injective(f) -> injective(compose(g, f))
proof
  @gen-g |
    fix g: Fn {
      @gen-f |
        fix f: Fn {
          @assume-g |
            assume injective(g) {
              @assume-f |
                assume injective(f) {
                  // unfold both injectivity hypotheses to their forall-forms
                  @inj-def |
                    forall h: Fn;
                      (injective(h) -> (forall a, b: Universe; apply(h, a) = apply(h, b) -> a = b))
                      and ((forall a, b: Universe; apply(h, a) = apply(h, b) -> a = b) -> injective(h))
                    [by axiom injectiveDef]
                  @g-at |
                    (injective(g) -> (forall a, b: Universe; apply(g, a) = apply(g, b) -> a = b))
                    and ((forall a, b: Universe; apply(g, a) = apply(g, b) -> a = b) -> injective(g))
                    [by forall_elim(g) inj-def]
                  @g-fwd |
                    injective(g) -> (forall a, b: Universe; apply(g, a) = apply(g, b) -> a = b)
                    [by and_elim_left g-at]
                  @g-hyp |
                    injective(g)
                    [by hypothesis assume-g]
                  @g-inj |
                    forall a, b: Universe; apply(g, a) = apply(g, b) -> a = b
                    [by modus_ponens g-fwd g-hyp]
                  @f-at |
                    (injective(f) -> (forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b))
                    and ((forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b) -> injective(f))
                    [by forall_elim(f) inj-def]
                  @f-fwd |
                    injective(f) -> (forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b)
                    [by and_elim_left f-at]
                  @f-hyp |
                    injective(f)
                    [by hypothesis assume-f]
                  @f-inj |
                    forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b
                    [by modus_ponens f-fwd f-hyp]
                  @body |
                    fix a: Universe {
                      @body2 |
                        fix b: Universe {
                          @assume-eq |
                            assume apply(compose(g, f), a) = apply(compose(g, f), b) {
                              @ca |
                                forall gg, ff: Fn; forall x: Universe;
                                  apply(compose(gg, ff), x) = apply(gg, apply(ff, x))
                                [by axiom composeApply]
                              @cgfa |
                                apply(compose(g, f), a) = apply(g, apply(f, a))
                                [by forall_elim(g, f, a) ca]
                              @cgfb |
                                apply(compose(g, f), b) = apply(g, apply(f, b))
                                [by forall_elim(g, f, b) ca]
                              @eq-hyp |
                                apply(compose(g, f), a) = apply(compose(g, f), b)
                                [by hypothesis assume-eq]
                              // g(f(a)) = g(f(b))
                              @gfa-eq-c |
                                apply(g, apply(f, a)) = apply(compose(g, f), b)
                                [by rewrite cgfa eq-hyp]
                              @gfa-eq-gfb |
                                apply(g, apply(f, a)) = apply(g, apply(f, b))
                                [by rewrite cgfb gfa-eq-c]
                              // g injective => f(a) = f(b)
                              @g-inj-at |
                                apply(g, apply(f, a)) = apply(g, apply(f, b)) -> apply(f, a) = apply(f, b)
                                [by forall_elim(apply(f, a), apply(f, b)) g-inj]
                              @fa-eq-fb |
                                apply(f, a) = apply(f, b)
                                [by modus_ponens g-inj-at gfa-eq-gfb]
                              // f injective => a = b
                              @f-inj-at |
                                apply(f, a) = apply(f, b) -> a = b
                                [by forall_elim(a, b) f-inj]
                              @a-eq-b |
                                a = b
                                [by modus_ponens f-inj-at fa-eq-fb]
                            }
                          @imp |
                            apply(compose(g, f), a) = apply(compose(g, f), b) -> a = b
                            [by implies_intro assume-eq]
                        }
                      @close-b |
                        forall b: Universe; apply(compose(g, f), a) = apply(compose(g, f), b) -> a = b
                        [by forall_intro body2]
                    }
                  @all |
                    forall a, b: Universe; apply(compose(g, f), a) = apply(compose(g, f), b) -> a = b
                    [by forall_intro body]
                  @c-at |
                    (injective(compose(g, f)) -> (forall a, b: Universe; apply(compose(g, f), a) = apply(compose(g, f), b) -> a = b))
                    and ((forall a, b: Universe; apply(compose(g, f), a) = apply(compose(g, f), b) -> a = b) -> injective(compose(g, f)))
                    [by forall_elim(compose(g, f)) inj-def]
                  @c-bwd |
                    (forall a, b: Universe; apply(compose(g, f), a) = apply(compose(g, f), b) -> a = b) -> injective(compose(g, f))
                    [by and_elim_right c-at]
                  @inj-c |
                    injective(compose(g, f))
                    [by modus_ponens c-bwd all]
                }
              @imp-f |
                injective(f) -> injective(compose(g, f))
                [by implies_intro assume-f]
            }
          @imp-g |
            injective(g) -> injective(f) -> injective(compose(g, f))
            [by implies_intro assume-g]
        }
      @close-f |
        forall f: Fn; injective(g) -> injective(f) -> injective(compose(g, f))
        [by forall_intro gen-f]
    }
  @conclusion |
    forall g, f: Fn; injective(g) -> injective(f) -> injective(compose(g, f))
    [by forall_intro gen-g]
qed
```

**(3) onto ∘ onto is onto** (the book's proof): given `c`, surjectivity of `g`
yields `b` with `g(b) = c`, then surjectivity of `f` yields `a` with
`f(a) = b`, and `(g∘f)(a) = g(f(a)) = g(b) = c`.

```bpa
// Theorem A.3: onto ∘ onto is onto (the book's proof (3)).
// Given c, g onto gives b with g(b)=c; f onto gives a with f(a)=b; then
// (g∘f)(a) = g(f(a)) = g(b) = c.
theorem composeSurjective: forall g, f: Fn;
  surjective(g) -> surjective(f) -> surjective(compose(g, f))
proof
  @gen-g |
    fix g: Fn {
      @gen-f |
        fix f: Fn {
          @assume-g |
            assume surjective(g) {
              @assume-f |
                assume surjective(f) {
                  @surj-def |
                    forall h: Fn;
                      (surjective(h) -> (forall y: Universe; exists x: Universe; apply(h, x) = y))
                      and ((forall y: Universe; exists x: Universe; apply(h, x) = y) -> surjective(h))
                    [by axiom surjectiveDef]
                  @g-at |
                    (surjective(g) -> (forall y: Universe; exists x: Universe; apply(g, x) = y))
                    and ((forall y: Universe; exists x: Universe; apply(g, x) = y) -> surjective(g))
                    [by forall_elim(g) surj-def]
                  @g-fwd |
                    surjective(g) -> (forall y: Universe; exists x: Universe; apply(g, x) = y)
                    [by and_elim_left g-at]
                  @g-hyp |
                    surjective(g)
                    [by hypothesis assume-g]
                  @g-onto |
                    forall y: Universe; exists x: Universe; apply(g, x) = y
                    [by modus_ponens g-fwd g-hyp]
                  @f-at |
                    (surjective(f) -> (forall y: Universe; exists x: Universe; apply(f, x) = y))
                    and ((forall y: Universe; exists x: Universe; apply(f, x) = y) -> surjective(f))
                    [by forall_elim(f) surj-def]
                  @f-fwd |
                    surjective(f) -> (forall y: Universe; exists x: Universe; apply(f, x) = y)
                    [by and_elim_left f-at]
                  @f-hyp |
                    surjective(f)
                    [by hypothesis assume-f]
                  @f-onto |
                    forall y: Universe; exists x: Universe; apply(f, x) = y
                    [by modus_ponens f-fwd f-hyp]
                  @body |
                    fix c: Universe {
                      // g onto: get b with g(b) = c
                      @g-at-c |
                        exists x: Universe; apply(g, x) = c
                        [by forall_elim(c) g-onto]
                      @unpack-b |
                        unpack b: Universe from g-at-c {
                          @gb-c |
                            apply(g, b) = c
                            [by hypothesis unpack-b]
                          // f onto: get a with f(a) = b
                          @f-at-b |
                            exists x: Universe; apply(f, x) = b
                            [by forall_elim(b) f-onto]
                          @unpack-a |
                            unpack a: Universe from f-at-b {
                              @fa-b |
                                apply(f, a) = b
                                [by hypothesis unpack-a]
                              @ca |
                                forall gg, ff: Fn; forall x: Universe;
                                  apply(compose(gg, ff), x) = apply(gg, apply(ff, x))
                                [by axiom composeApply]
                              @cgf-a |
                                apply(compose(g, f), a) = apply(g, apply(f, a))
                                [by forall_elim(g, f, a) ca]
                              // g(f(a)) = g(b) = c
                              @g-of-fa |
                                apply(compose(g, f), a) = apply(g, b)
                                [by rewrite fa-b cgf-a]
                              @cgf-a-c |
                                apply(compose(g, f), a) = c
                                [by rewrite gb-c g-of-fa]
                              @witness |
                                exists x: Universe; apply(compose(g, f), x) = c
                                [by exists_intro(a) cgf-a-c]
                            }
                          @exported |
                            exists x: Universe; apply(compose(g, f), x) = c
                            [by exists_elim unpack-a]
                        }
                      @c-hit |
                        exists x: Universe; apply(compose(g, f), x) = c
                        [by exists_elim unpack-b]
                    }
                  @all |
                    forall y: Universe; exists x: Universe; apply(compose(g, f), x) = y
                    [by forall_intro body]
                  @c-at |
                    (surjective(compose(g, f)) -> (forall y: Universe; exists x: Universe; apply(compose(g, f), x) = y))
                    and ((forall y: Universe; exists x: Universe; apply(compose(g, f), x) = y) -> surjective(compose(g, f)))
                    [by forall_elim(compose(g, f)) surj-def]
                  @c-bwd |
                    (forall y: Universe; exists x: Universe; apply(compose(g, f), x) = y) -> surjective(compose(g, f))
                    [by and_elim_right c-at]
                  @surj-c |
                    surjective(compose(g, f))
                    [by modus_ponens c-bwd all]
                }
              @imp-f |
                surjective(f) -> surjective(compose(g, f))
                [by implies_intro assume-f]
            }
          @imp-g |
            surjective(g) -> surjective(f) -> surjective(compose(g, f))
            [by implies_intro assume-g]
        }
      @close-f |
        forall f: Fn; surjective(g) -> surjective(f) -> surjective(compose(g, f))
        [by forall_intro gen-f]
    }
  @conclusion |
    forall g, f: Fn; surjective(g) -> surjective(f) -> surjective(compose(g, f))
    [by forall_intro gen-g]
qed
```

**(4) bijective ∘ bijective is bijective** follows from (2) and (3) — reading
"bijective" as `injective and surjective`, exactly the book's definition.

```bpa
// Theorem A.4: bij ∘ bij is bij (bijective = injective and surjective).
theorem composeBijective: forall g, f: Fn;
  (injective(g) and surjective(g)) -> (injective(f) and surjective(f))
  -> (injective(compose(g, f)) and surjective(compose(g, f)))
proof
  @gen-g |
    fix g: Fn {
      @gen-f |
        fix f: Fn {
          @assume-g |
            assume injective(g) and surjective(g) {
              @assume-f |
                assume injective(f) and surjective(f) {
                  @hg | injective(g) and surjective(g) [by hypothesis assume-g]
                  @hf | injective(f) and surjective(f) [by hypothesis assume-f]
                  @ig | injective(g) [by and_elim_left hg]
                  @sg | surjective(g) [by and_elim_right hg]
                  @if | injective(f) [by and_elim_left hf]
                  @sf | surjective(f) [by and_elim_right hf]
                  @ci-thm |
                    forall gg, ff: Fn; injective(gg) -> injective(ff) -> injective(compose(gg, ff))
                    [by theorem composeInjective]
                  @ci-at |
                    injective(g) -> injective(f) -> injective(compose(g, f))
                    [by forall_elim(g, f) ci-thm]
                  @ci1 | injective(f) -> injective(compose(g, f)) [by modus_ponens ci-at ig]
                  @inj-c | injective(compose(g, f)) [by modus_ponens ci1 if]
                  @cs-thm |
                    forall gg, ff: Fn; surjective(gg) -> surjective(ff) -> surjective(compose(gg, ff))
                    [by theorem composeSurjective]
                  @cs-at |
                    surjective(g) -> surjective(f) -> surjective(compose(g, f))
                    [by forall_elim(g, f) cs-thm]
                  @cs1 | surjective(f) -> surjective(compose(g, f)) [by modus_ponens cs-at sg]
                  @surj-c | surjective(compose(g, f)) [by modus_ponens cs1 sf]
                  @both |
                    injective(compose(g, f)) and surjective(compose(g, f))
                    [by and_intro inj-c surj-c]
                }
              @imp-f |
                (injective(f) and surjective(f)) -> (injective(compose(g, f)) and surjective(compose(g, f)))
                [by implies_intro assume-f]
            }
          @imp-g |
            (injective(g) and surjective(g)) -> (injective(f) and surjective(f))
            -> (injective(compose(g, f)) and surjective(compose(g, f)))
            [by implies_intro assume-g]
        }
      @close-f |
        forall f: Fn;
          (injective(g) and surjective(g)) -> (injective(f) and surjective(f))
          -> (injective(compose(g, f)) and surjective(compose(g, f)))
        [by forall_intro gen-f]
    }
  @conclusion |
    forall g, f: Fn;
      (injective(g) and surjective(g)) -> (injective(f) and surjective(f))
      -> (injective(compose(g, f)) and surjective(compose(g, f)))
    [by forall_intro gen-g]
qed
```

**Proof (book).** We will prove (1) and (3). Part (2) is left as an exercise. Part (4) follows directly from (2) and (3).

(1) We must show that

$$h \circ (g \circ f) = (h \circ g) \circ f$$.

For $a \in A$ we have

$$\begin{aligned}
(h \circ (g \circ f))(a) & = h((g \circ f)(a)) \\
& = h(g(f(a))) \\
& = (h \circ g)(f(a)) \\
& = ((h \circ g) \circ f)(a)
\end{aligned}$$.

(3) Assume that $f$ and $g$ are both onto functions. Given $c \in C$, we must show that there exists an $a \in A$ such that $(g \circ f)(a) = g(f(a)) = c$. However, since $g$ is onto, there is an element $b \in B$ such that $g(b) = c$. Similarly, there is an $a \in A$ such that $f(a) = b$. Accordingly,

$$(g \circ f)(a) = g(f(a)) = g(b) = c$$.

If $S$ is any set, we will use $\operatorname{id}_S$ or $\operatorname{id}$ to denote the **identity mapping** from $S$ to itself. Define this map by $\operatorname{id}(s) = s$ for all $s \in S$. A map $g: B \rightarrow A$ is an **inverse mapping** of $f: A \rightarrow B$ if $g \circ f = \operatorname{id}_A$ and $f \circ g = \operatorname{id}_B$; in other words, the inverse function of a function simply "undoes" the function. A map is said to be **invertible** if it has an inverse. We usually write $f^{-1}$ for the inverse of $f$.

**Example.** The function $f(x) = x^3$ has inverse $f^{-1}(x) = \sqrt[3]{x}$ by the earlier commuting-composition example.

**Example.** The natural logarithm and the exponential functions, $f(x) = \ln x$ and $f^{-1}(x) = e^x$, are inverses of each other provided that we are careful about choosing domains. Observe that

$$f(f^{-1}(x)) = f(e^x) = \ln e^x = x$$

and

$$f^{-1}(f(x)) = f^{-1}(\ln x) = e^{\ln x} = x$$

whenever composition makes sense.

**Example.** Suppose that

$$A =
\begin{pmatrix}
3 & 1 \\
5 & 2
\end{pmatrix}$$.

Then $A$ defines a map from ${\mathbb R}^2$ to ${\mathbb R}^2$ by

$$T_A (x,y) = (3x +  y, 5x + 2y)$$.

We can find an inverse map of $T_A$ by simply inverting the matrix $A$; that is, $T_A^{-1} = T_{A^{-1}}$. In this example,

$$A^{-1} =
\begin{pmatrix}
2  & -1 \\
-5 &  3
\end{pmatrix};$$

hence, the inverse map is given by

$$T_A^{-1} (x,y) = (2x -  y, -5x + 3y)$$.

It is easy to check that

$$T^{-1}_A \circ T_A (x,y) = T_A \circ T_A^{-1} (x,y) = (x,y)$$.

Not every map has an inverse. If we consider the map

$$T_B (x,y) = (3x , 0 )$$

given by the matrix

$$B =
\begin{pmatrix}
3 & 0 \\
0 & 0
\end{pmatrix}$$,

then an inverse map would have to be of the form

$$T_B^{-1} (x,y) = (ax + by, cx +dy)$$

and

$$(x,y) = T_B \circ T_B^{-1} (x,y) = (3ax + 3by, 0)$$

for all $x$ and $y$. Clearly this is impossible because $y$ might not be $0$.

**Example.** Given the permutation

$$\pi =
\begin{pmatrix}
1 & 2 & 3 \\
2 & 3 & 1
\end{pmatrix}$$

on $S = \{ 1,2,3 \}$, it is easy to see that the permutation defined by

$$\pi^{-1} =
\begin{pmatrix}
1 & 2 & 3 \\
3 & 1 & 2
\end{pmatrix}$$

is the inverse of $\pi$. In fact, any bijective mapping possesses an inverse, as we will see in the next theorem.

## Theorem

> A mapping is invertible if and only if it is both one-to-one and onto.

Reading "bijective" as `injective and surjective`, the biconditional splits
into two implications. We prove the **forward** direction (invertible ⇒
bijective) and mark the **backward** direction, which `bpa` cannot yet encode.

**Forward — invertible ⇒ injective.** From `g∘f = id` we get `g(f(a)) = a`, so
`f(a₁) = f(a₂)` forces `a₁ = g(f(a₁)) = g(f(a₂)) = a₂`.

```bpa
// Theorem B, forward (part 1): invertible ⇒ injective.
theorem invertibleImpliesInjective: forall f: Fn; invertible(f) -> injective(f)
proof
  @gen-f |
    fix f: Fn {
      @assume-inv |
        assume invertible(f) {
          @inv-def |
            forall ff: Fn;
              (invertible(ff) ->
                (exists gg: Fn; compose(gg, ff) = id and compose(ff, gg) = id))
              and ((exists gg: Fn; compose(gg, ff) = id and compose(ff, gg) = id)
                -> invertible(ff))
            [by axiom invertibleDef]
          @inv-at |
            (invertible(f) ->
              (exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id))
            and ((exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id)
              -> invertible(f))
            [by forall_elim(f) inv-def]
          @fwd-imp |
            invertible(f) ->
              (exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id)
            [by and_elim_left inv-at]
          @inv-hyp |
            invertible(f)
            [by hypothesis assume-inv]
          @exists-g |
            exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id
            [by modus_ponens fwd-imp inv-hyp]
          @unpacked |
            unpack g: Fn from exists-g {
              @g-props |
                compose(g, f) = id and compose(f, g) = id
                [by hypothesis unpacked]
              @gf-id |
                compose(g, f) = id
                [by and_elim_left g-props]
              // now show injectivity: f(a)=f(b) -> a=b
              @inj-body |
                fix a: Universe {
                  @inj-body2 |
                    fix b: Universe {
                      @assume-eq |
                        assume apply(f, a) = apply(f, b) {
                          @ca |
                            forall gg, ff: Fn; forall x: Universe;
                              apply(compose(gg, ff), x) = apply(gg, apply(ff, x))
                            [by axiom composeApply]
                          // g(f(a)) = (g∘f)(a) = id(a) = a  ; same for b
                          @gfa |
                            apply(compose(g, f), a) = apply(g, apply(f, a))
                            [by forall_elim(g, f, a) ca]
                          @gfb |
                            apply(compose(g, f), b) = apply(g, apply(f, b))
                            [by forall_elim(g, f, b) ca]
                          @id-app |
                            forall x: Universe; apply(id, x) = x
                            [by axiom identityApply]
                          // (g∘f)(a) = a: rewrite compose(g,f)->id in gfa's LHS,
                          // then id(a)->a.
                          @gfa-id |
                            apply(id, a) = apply(g, apply(f, a))
                            [by rewrite gf-id gfa]
                          @id-a |
                            apply(id, a) = a
                            [by forall_elim(a) id-app]
                          @a-eq-gfa |
                            a = apply(g, apply(f, a))
                            [by rewrite id-a gfa-id]
                          @lhs-a |
                            apply(g, apply(f, a)) = a
                            [by symmetry a-eq-gfa]
                          @gfb-id |
                            apply(id, b) = apply(g, apply(f, b))
                            [by rewrite gf-id gfb]
                          @id-b |
                            apply(id, b) = b
                            [by forall_elim(b) id-app]
                          @b-eq-gfb |
                            b = apply(g, apply(f, b))
                            [by rewrite id-b gfb-id]
                          @lhs-b |
                            apply(g, apply(f, b)) = b
                            [by symmetry b-eq-gfb]
                          // f(a)=f(b) => g(f(a))=g(f(b)); chain to a=b
                          @eq-hyp |
                            apply(f, a) = apply(f, b)
                            [by hypothesis assume-eq]
                          @gfa-refl |
                            apply(g, apply(f, a)) = apply(g, apply(f, a))
                            [by reflexivity]
                          @gfa-eq-gfb |
                            apply(g, apply(f, a)) = apply(g, apply(f, b))
                            [by rewrite eq-hyp gfa-refl]
                          // a = g(f(a)) = g(f(b)) = b
                          @a-eq-gfb |
                            a = apply(g, apply(f, b))
                            [by rewrite lhs-a gfa-eq-gfb]
                          @a-eq-b |
                            a = b
                            [by rewrite lhs-b a-eq-gfb]
                        }
                      @imp-b |
                        apply(f, a) = apply(f, b) -> a = b
                        [by implies_intro assume-eq]
                    }
                  @close-b |
                    forall b: Universe; apply(f, a) = apply(f, b) -> a = b
                    [by forall_intro inj-body2]
                }
              @inj-all |
                forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b
                [by forall_intro inj-body]
              @inj-def |
                forall ff: Fn;
                  (injective(ff) -> (forall a, b: Universe; apply(ff, a) = apply(ff, b) -> a = b))
                  and ((forall a, b: Universe; apply(ff, a) = apply(ff, b) -> a = b) -> injective(ff))
                [by axiom injectiveDef]
              @inj-at |
                (injective(f) -> (forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b))
                and ((forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b) -> injective(f))
                [by forall_elim(f) inj-def]
              @inj-bwd |
                (forall a, b: Universe; apply(f, a) = apply(f, b) -> a = b) -> injective(f)
                [by and_elim_right inj-at]
              @injective-f |
                injective(f)
                [by modus_ponens inj-bwd inj-all]
            }
          @inj-out |
            injective(f)
            [by exists_elim unpacked]
        }
      @imp |
        invertible(f) -> injective(f)
        [by implies_intro assume-inv]
    }
  @conclusion |
    forall f: Fn; invertible(f) -> injective(f)
    [by forall_intro gen-f]
qed
```

**Forward — invertible ⇒ surjective.** From `f∘g = id` we get `f(g(b)) = b`, so
`x = g(b)` is a preimage of any `b`.

```bpa
// Theorem B, forward (part 2): invertible ⇒ surjective.
// From f∘g = id: for any y, f(g(y)) = y, so x := g(y) is a preimage.
theorem invertibleImpliesSurjective: forall f: Fn; invertible(f) -> surjective(f)
proof
  @gen-f |
    fix f: Fn {
      @assume-inv |
        assume invertible(f) {
          @inv-def |
            forall ff: Fn;
              (invertible(ff) ->
                (exists gg: Fn; compose(gg, ff) = id and compose(ff, gg) = id))
              and ((exists gg: Fn; compose(gg, ff) = id and compose(ff, gg) = id)
                -> invertible(ff))
            [by axiom invertibleDef]
          @inv-at |
            (invertible(f) ->
              (exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id))
            and ((exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id)
              -> invertible(f))
            [by forall_elim(f) inv-def]
          @fwd-imp |
            invertible(f) ->
              (exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id)
            [by and_elim_left inv-at]
          @inv-hyp |
            invertible(f)
            [by hypothesis assume-inv]
          @exists-g |
            exists gg: Fn; compose(gg, f) = id and compose(f, gg) = id
            [by modus_ponens fwd-imp inv-hyp]
          @unpacked |
            unpack g: Fn from exists-g {
              @g-props |
                compose(g, f) = id and compose(f, g) = id
                [by hypothesis unpacked]
              @fg-id |
                compose(f, g) = id
                [by and_elim_right g-props]
              @surj-body |
                fix y: Universe {
                  // witness x = g(y): f(g(y)) = (f∘g)(y) = id(y) = y
                  @ca |
                    forall gg, ff: Fn; forall x: Universe;
                      apply(compose(gg, ff), x) = apply(gg, apply(ff, x))
                    [by axiom composeApply]
                  @fgy |
                    apply(compose(f, g), y) = apply(f, apply(g, y))
                    [by forall_elim(f, g, y) ca]
                  @id-app |
                    forall x: Universe; apply(id, x) = x
                    [by axiom identityApply]
                  @fgy-id |
                    apply(id, y) = apply(f, apply(g, y))
                    [by rewrite fg-id fgy]
                  @id-y |
                    apply(id, y) = y
                    [by forall_elim(y) id-app]
                  @y-eq |
                    y = apply(f, apply(g, y))
                    [by rewrite id-y fgy-id]
                  @f-hits |
                    apply(f, apply(g, y)) = y
                    [by symmetry y-eq]
                  @witness |
                    exists x: Universe; apply(f, x) = y
                    [by exists_intro(apply(g, y)) f-hits]
                }
              @surj-all |
                forall y: Universe; exists x: Universe; apply(f, x) = y
                [by forall_intro surj-body]
              @surj-def |
                forall ff: Fn;
                  (surjective(ff) -> (forall y: Universe; exists x: Universe; apply(ff, x) = y))
                  and ((forall y: Universe; exists x: Universe; apply(ff, x) = y) -> surjective(ff))
                [by axiom surjectiveDef]
              @surj-at |
                (surjective(f) -> (forall y: Universe; exists x: Universe; apply(f, x) = y))
                and ((forall y: Universe; exists x: Universe; apply(f, x) = y) -> surjective(f))
                [by forall_elim(f) surj-def]
              @surj-bwd |
                (forall y: Universe; exists x: Universe; apply(f, x) = y) -> surjective(f)
                [by and_elim_right surj-at]
              @surjective-f |
                surjective(f)
                [by modus_ponens surj-bwd surj-all]
            }
          @surj-out |
            surjective(f)
            [by exists_elim unpacked]
        }
      @imp |
        invertible(f) -> surjective(f)
        [by implies_intro assume-inv]
    }
  @conclusion |
    forall f: Fn; invertible(f) -> surjective(f)
    [by forall_intro gen-f]
qed
```

**Forward — invertible ⇒ bijective** is the conjunction of the two.

```bpa
// Theorem B, forward (combined): invertible ⇒ bijective.
theorem invertibleImpliesBijective: forall f: Fn;
  invertible(f) -> (injective(f) and surjective(f))
proof
  @gen-f |
    fix f: Fn {
      @assume-inv |
        assume invertible(f) {
          @inv-hyp | invertible(f) [by hypothesis assume-inv]
          @ii-thm | forall ff: Fn; invertible(ff) -> injective(ff) [by theorem invertibleImpliesInjective]
          @ii-at | invertible(f) -> injective(f) [by forall_elim(f) ii-thm]
          @inj-f | injective(f) [by modus_ponens ii-at inv-hyp]
          @is-thm | forall ff: Fn; invertible(ff) -> surjective(ff) [by theorem invertibleImpliesSurjective]
          @is-at | invertible(f) -> surjective(f) [by forall_elim(f) is-thm]
          @surj-f | surjective(f) [by modus_ponens is-at inv-hyp]
          @both | injective(f) and surjective(f) [by and_intro inj-f surj-f]
        }
      @imp | invertible(f) -> (injective(f) and surjective(f)) [by implies_intro assume-inv]
    }
  @conclusion |
    forall f: Fn; invertible(f) -> (injective(f) and surjective(f))
    [by forall_intro gen-f]
qed
```

**Backward — bijective ⇒ invertible — cannot currently be encoded.**

```bpa
// this direction cannot currently be encoded [needs a choice /
// inverse-construction operator]: the book's proof builds the inverse g by
// "letting g(b) = a", where a is the unique preimage of b under the bijection
// f. That is a definite description — constructing an Fn object from a
// per-point specification (b |-> the unique a with f(a) = b). bpa's
// first-order logic has no operator that turns "for each b there exists a
// unique a" into a function value, so the witnessing g cannot be named, and
// invertibleDef's `exists g` cannot be discharged. Deferred; see aata/README.
```

**Proof (book).** Suppose first that $f:A \rightarrow B$ is invertible with inverse $g: B \rightarrow A$. Then $g \circ f = \operatorname{id}_A$ is the identity map; that is, $g(f(a)) = a$. If $a_1, a_2 \in A$ with $f(a_1) = f(a_2)$, then $a_1 = g(f(a_1)) = g(f(a_2)) = a_2$. Consequently, $f$ is one-to-one. Now suppose that $b \in B$. To show that $f$ is onto, it is necessary to find an $a \in A$ such that $f(a) = b$, but $f(g(b)) = b$ with $g(b) \in A$. Let $a = g(b)$.

Conversely, let $f$ be bijective and let $b \in B$. Since $f$ is onto, there exists an $a \in A$ such that $f(a) = b$. Because $f$ is one-to-one, $a$ must be unique. Define $g$ by letting $g(b) = a$. We have now constructed the inverse of $f$.

---

## Deferred to a later file

- **§1.2.3 Equivalence Relations and Partitions** — the rest of Chapter 1 — is
  deferred: it needs a relation sort and sets-of-sets / quotient structure
  (equivalence classes, partitions) that neither `std/set.bpa` nor
  `std/function.bpa` models. See `aata/README`.
