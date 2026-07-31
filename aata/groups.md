# Groups — Basic Properties

A literate bpa translation of the "Basic Properties of Groups" results from
Chapter 3 of Thomas W. Judson's *Abstract Algebra: Theory and Applications*
(see `vendor/aata/src/groups.xml`; © 1997–2025 Judson, GFDL 1.3). Each `bpa`
block below is checked by `bpa check aata/groups.md`; the proofs follow the
textbook's own arguments.

The theory of a group lives in `std/group.bpa` (a sort `Grp`, an associative
operation `op`, a two-sided identity `E`, and a two-sided `inverse`). Here we
import it and alias the vocabulary to the **book's notation** — `G`, `e`, `op`,
`inv` — so the proofs read like the text.

```bpa
import group <<< "std/group.bpa"

// The book's notation, aliased onto std/group.bpa's (longer) library names.
sort G = group.Grp
const e = group.E
func op = group.op
func inv = group.inverse
axiom associative = group.opAssoc
axiom identityLeft = group.opIdentityLeft
axiom identityRight = group.opIdentityRight
axiom inverseLeft = group.opInverseLeft
axiom inverseRight = group.opInverseRight
```

## Proposition — the identity is unique

> The identity element in a group $G$ is unique.

The textbook argues: if $e$ and $e'$ are both identities, then $e = ee' = e'$.
We state uniqueness as: **any left identity `x` equals `e`** — because
`x = op(x, e) = e` (the left `x` sends `e` to `e`; `identityRight` sends it to
`x`).

```bpa
theorem identityUnique: forall x: G; (forall g: G; op(x, g) = g) -> x = e
proof
  @generalize-x |
    fix x: G {
      @given |
        assume forall g: G; op(x, g) = g {
          @x-left-id |
            forall g: G; op(x, g) = g
            [by hypothesis given]
          @x-times-e-is-e |
            op(x, e) = e
            [by forall_elim(e) x-left-id]
          @id-right |
            forall a: G; op(a, e) = a
            [by axiom identityRight]
          @x-times-e-is-x |
            op(x, e) = x
            [by forall_elim(x) id-right]
          @x-is-e |
            x = e
            [by rewrite x-times-e-is-x x-times-e-is-e]
        }
      @discharge |
        (forall g: G; op(x, g) = g) -> x = e
        [by implies_intro given]
    }
  @conclusion |
    forall x: G; (forall g: G; op(x, g) = g) -> x = e
    [by forall_intro generalize-x]
qed
```

## Proposition — inverses are unique

> If $g$ is any element in a group $G$, then the inverse of $g$ is unique.

The reusable form: **a right inverse of `a` is exactly `inv(a)`** — if
`op(a, b) = e` then `b = inv(a)`. The proof:
`b = eb = (a⁻¹a)b = a⁻¹(ab) = a⁻¹e = a⁻¹`. The re-association `(a⁻¹a)b → a⁻¹(ab)`
is a single `assoc(associative)` step.

```bpa
theorem inverseUnique: forall a, b: G; op(a, b) = e -> b = inv(a)
proof
  @generalize-a |
    fix a: G {
      @generalize-b |
        fix b: G {
          @given |
            assume op(a, b) = e {
              @ab-is-e |
                op(a, b) = e
                [by hypothesis given]
              @id-left |
                forall g: G; op(e, g) = g
                [by axiom identityLeft]
              @b-eq |
                op(e, b) = b
                [by forall_elim(b) id-left]
              @b-is-eb |
                b = op(e, b)
                [by symmetry b-eq]
              @inv-left |
                forall g: G; op(inv(g), g) = e
                [by axiom inverseLeft]
              @inva-a-is-e |
                op(inv(a), a) = e
                [by forall_elim(a) inv-left]
              @e-is-inva-a |
                e = op(inv(a), a)
                [by symmetry inva-a-is-e]
              @b-is-inva-a-b |
                b = op(op(inv(a), a), b)
                [by rewrite e-is-inva-a b-is-eb]
              @assoc-step |
                op(op(inv(a), a), b) = op(inv(a), op(a, b))
                [by assoc(associative)]
              @b-is-inva-ab |
                b = op(inv(a), op(a, b))
                [by rewrite assoc-step b-is-inva-a-b]
              @b-is-inva-e |
                b = op(inv(a), e)
                [by rewrite ab-is-e b-is-inva-ab]
              @id-right |
                forall g: G; op(g, e) = g
                [by axiom identityRight]
              @inva-e-is-inva |
                op(inv(a), e) = inv(a)
                [by forall_elim(inv(a)) id-right]
              @b-is-inva |
                b = inv(a)
                [by rewrite inva-e-is-inva b-is-inva-e]
            }
          @discharge |
            op(a, b) = e -> b = inv(a)
            [by implies_intro given]
        }
      @close-b |
        forall b: G; op(a, b) = e -> b = inv(a)
        [by forall_intro generalize-b]
    }
  @conclusion |
    forall a, b: G; op(a, b) = e -> b = inv(a)
    [by forall_intro generalize-a]
qed
```

## Proposition — $(a^{-1})^{-1} = a$

> For any $a \in G$, $(a^{-1})^{-1} = a$.

Since `op(inv(a), a) = e`, the element `a` is a right inverse of `inv(a)`, so by
`inverseUnique`, `a = inv(inv(a))`.

```bpa
theorem invInvolution: forall a: G; inv(inv(a)) = a
proof
  @generalize-a |
    fix a: G {
      @inv-left |
        forall g: G; op(inv(g), g) = e
        [by axiom inverseLeft]
      @inva-a-is-e |
        op(inv(a), a) = e
        [by forall_elim(a) inv-left]
      @inv-unique |
        forall x, y: G; op(x, y) = e -> y = inv(x)
        [by theorem inverseUnique]
      @at-inva-a |
        op(inv(a), a) = e -> a = inv(inv(a))
        [by forall_elim(inv(a), a) inv-unique]
      @a-is-invinva |
        a = inv(inv(a))
        [by modus_ponens at-inva-a inva-a-is-e]
      @invinva-is-a |
        inv(inv(a)) = a
        [by symmetry a-is-invinva]
    }
  @conclusion |
    forall a: G; inv(inv(a)) = a
    [by forall_intro generalize-a]
qed
```

## Proposition — $(ab)^{-1} = b^{-1} a^{-1}$

> Let $G$ be a group. If $a, b \in G$, then $(ab)^{-1} = b^{-1} a^{-1}$.

The textbook shows $abb^{-1}a^{-1} = e$; then by uniqueness of inverses,
$(ab)^{-1} = b^{-1}a^{-1}$. We compute `op(op(a,b), op(inv(b), inv(a)))`,
re-associating (via `assoc`) to `a·(b·b⁻¹)·a⁻¹`, which collapses to `e`, and
apply `inverseUnique`.

```bpa
theorem invProduct: forall a, b: G; inv(op(a, b)) = op(inv(b), inv(a))
proof
  @generalize-a |
    fix a: G {
      @generalize-b |
        fix b: G {
          @rearrange |
            op(op(a, b), op(inv(b), inv(a))) = op(a, op(op(b, inv(b)), inv(a)))
            [by assoc(associative)]
          @b-invb |
            forall g: G; op(g, inv(g)) = e
            [by axiom inverseRight]
          @b-invb-is-e |
            op(b, inv(b)) = e
            [by forall_elim(b) b-invb]
          @after-bb |
            op(op(a, b), op(inv(b), inv(a))) = op(a, op(e, inv(a)))
            [by rewrite b-invb-is-e rearrange]
          @id-left |
            forall g: G; op(e, g) = g
            [by axiom identityLeft]
          @e-inva |
            op(e, inv(a)) = inv(a)
            [by forall_elim(inv(a)) id-left]
          @after-einva |
            op(op(a, b), op(inv(b), inv(a))) = op(a, inv(a))
            [by rewrite e-inva after-bb]
          @a-inva |
            op(a, inv(a)) = e
            [by forall_elim(a) b-invb]
          @product-is-e |
            op(op(a, b), op(inv(b), inv(a))) = e
            [by rewrite a-inva after-einva]
          @inv-unique |
            forall x, y: G; op(x, y) = e -> y = inv(x)
            [by theorem inverseUnique]
          @at-prod |
            op(op(a, b), op(inv(b), inv(a))) = e -> op(inv(b), inv(a)) = inv(op(a, b))
            [by forall_elim(op(a, b), op(inv(b), inv(a))) inv-unique]
          @rhs-is-inv |
            op(inv(b), inv(a)) = inv(op(a, b))
            [by modus_ponens at-prod product-is-e]
          @conclusion-inner |
            inv(op(a, b)) = op(inv(b), inv(a))
            [by symmetry rhs-is-inv]
        }
      @close-b |
        forall b: G; inv(op(a, b)) = op(inv(b), inv(a))
        [by forall_intro generalize-b]
    }
  @conclusion |
    forall a, b: G; inv(op(a, b)) = op(inv(b), inv(a))
    [by forall_intro generalize-a]
qed
```

## Proposition — cancellation

> If $G$ is a group and $a, b, c \in G$, then $ba = ca$ implies $b = c$ (and
> $ab = ac$ implies $b = c$).

The book leaves this as an exercise (Exercise 30). We prove **right
cancellation**: right-multiply `op(b, a) = op(c, a)` by `inv(a)` and simplify
each side via `b·(a·a⁻¹) = b·e = b`.

```bpa
theorem cancelRight: forall a, b, c: G; op(b, a) = op(c, a) -> b = c
proof
  @generalize-a |
    fix a: G {
      @generalize-b |
        fix b: G {
          @generalize-c |
            fix c: G {
              @given |
                assume op(b, a) = op(c, a) {
                  @hyp |
                    op(b, a) = op(c, a)
                    [by hypothesis given]
                  @hyp-refl |
                    op(op(b, a), inv(a)) = op(op(b, a), inv(a))
                    [by reflexivity]
                  @mult |
                    op(op(b, a), inv(a)) = op(op(c, a), inv(a))
                    [by rewrite hyp hyp-refl]
                  @assoc-b |
                    op(op(b, a), inv(a)) = op(b, op(a, inv(a)))
                    [by assoc(associative)]
                  @a-inva |
                    forall g: G; op(g, inv(g)) = e
                    [by axiom inverseRight]
                  @a-inva-is-e |
                    op(a, inv(a)) = e
                    [by forall_elim(a) a-inva]
                  @assoc-b-e |
                    op(op(b, a), inv(a)) = op(b, e)
                    [by rewrite a-inva-is-e assoc-b]
                  @id-right |
                    forall g: G; op(g, e) = g
                    [by axiom identityRight]
                  @b-e-is-b |
                    op(b, e) = b
                    [by forall_elim(b) id-right]
                  @lhs-is-b |
                    op(op(b, a), inv(a)) = b
                    [by rewrite b-e-is-b assoc-b-e]
                  @assoc-c |
                    op(op(c, a), inv(a)) = op(c, op(a, inv(a)))
                    [by assoc(associative)]
                  @assoc-c-e |
                    op(op(c, a), inv(a)) = op(c, e)
                    [by rewrite a-inva-is-e assoc-c]
                  @c-e-is-c |
                    op(c, e) = c
                    [by forall_elim(c) id-right]
                  @rhs-is-c |
                    op(op(c, a), inv(a)) = c
                    [by rewrite c-e-is-c assoc-c-e]
                  @b-is-mult |
                    b = op(op(b, a), inv(a))
                    [by symmetry lhs-is-b]
                  @b-is-rhs |
                    b = op(op(c, a), inv(a))
                    [by rewrite mult b-is-mult]
                  @b-is-c |
                    b = c
                    [by rewrite rhs-is-c b-is-rhs]
                }
              @discharge |
                op(b, a) = op(c, a) -> b = c
                [by implies_intro given]
            }
          @close-c |
            forall c: G; op(b, a) = op(c, a) -> b = c
            [by forall_intro generalize-c]
        }
      @close-b |
        forall b, c: G; op(b, a) = op(c, a) -> b = c
        [by forall_intro generalize-b]
    }
  @conclusion |
    forall a, b, c: G; op(b, a) = op(c, a) -> b = c
    [by forall_intro generalize-a]
qed
```

# Exercises

Solutions to the Chapter 3 exercises that are provable from the group axioms
alone (no additional machinery). Exercises that need structure bpa does not yet
have — a concrete $\mathbb{Z}_n$ model, finite sets and counting, matrix groups
— are listed with a `#### Solution` note stating what they would require; those
are the forcing-function backlog for future standard-library work.

## Exercise 30 — cancellation laws

> Prove the right and left cancellation laws for a group $G$.

#### Solution

Right cancellation is the `cancelRight` proposition above. Left cancellation is
its mirror (right-multiply becomes left-multiply by `inv(a)`):

```bpa
theorem cancelLeft: forall a, b, c: G; op(a, b) = op(a, c) -> b = c
proof
  @generalize-a |
    fix a: G {
      @generalize-b |
        fix b: G {
          @generalize-c |
            fix c: G {
              @given |
                assume op(a, b) = op(a, c) {
                  @hyp |
                    op(a, b) = op(a, c)
                    [by hypothesis given]
                  @hyp-refl |
                    op(inv(a), op(a, b)) = op(inv(a), op(a, b))
                    [by reflexivity]
                  @mult |
                    op(inv(a), op(a, b)) = op(inv(a), op(a, c))
                    [by rewrite hyp hyp-refl]
                  @assoc-b |
                    op(op(inv(a), a), b) = op(inv(a), op(a, b))
                    [by assoc(associative)]
                  @inv-left |
                    forall g: G; op(inv(g), g) = e
                    [by axiom inverseLeft]
                  @inva-a-is-e |
                    op(inv(a), a) = e
                    [by forall_elim(a) inv-left]
                  @lhs1 |
                    op(e, b) = op(inv(a), op(a, b))
                    [by rewrite inva-a-is-e assoc-b]
                  @id-left |
                    forall g: G; op(e, g) = g
                    [by axiom identityLeft]
                  @e-b-is-b |
                    op(e, b) = b
                    [by forall_elim(b) id-left]
                  @b-is-lhs |
                    b = op(inv(a), op(a, b))
                    [by rewrite e-b-is-b lhs1]
                  @b-is-rhs |
                    b = op(inv(a), op(a, c))
                    [by rewrite mult b-is-lhs]
                  @assoc-c |
                    op(op(inv(a), a), c) = op(inv(a), op(a, c))
                    [by assoc(associative)]
                  @rhs1 |
                    op(e, c) = op(inv(a), op(a, c))
                    [by rewrite inva-a-is-e assoc-c]
                  @e-c-is-c |
                    op(e, c) = c
                    [by forall_elim(c) id-left]
                  @c-is-rhs |
                    c = op(inv(a), op(a, c))
                    [by rewrite e-c-is-c rhs1]
                  @rhs-is-c |
                    op(inv(a), op(a, c)) = c
                    [by symmetry c-is-rhs]
                  @b-is-c |
                    b = c
                    [by rewrite rhs-is-c b-is-rhs]
                }
              @discharge |
                op(a, b) = op(a, c) -> b = c
                [by implies_intro given]
            }
          @close-c |
            forall c: G; op(a, b) = op(a, c) -> b = c
            [by forall_intro generalize-c]
        }
      @close-b |
        forall b, c: G; op(a, b) = op(a, c) -> b = c
        [by forall_intro generalize-b]
    }
  @conclusion |
    forall a, b, c: G; op(a, b) = op(a, c) -> b = c
    [by forall_intro generalize-a]
qed
```

## Exercise 28 — unique solution of $xa = b$

> If $G$ is a group and $a, b \in G$, the equation $xa = b$ has a unique
> solution in $G$.

#### Solution

**Existence** — the solution is $x = b a^{-1}$:

```bpa
theorem solutionExists: forall a, b: G; op(op(b, inv(a)), a) = b
proof
  @generalize-a |
    fix a: G {
      @generalize-b |
        fix b: G {
          @assoc-step |
            op(op(b, inv(a)), a) = op(b, op(inv(a), a))
            [by assoc(associative)]
          @inv-left |
            forall g: G; op(inv(g), g) = e
            [by axiom inverseLeft]
          @inva-a |
            op(inv(a), a) = e
            [by forall_elim(a) inv-left]
          @with-e |
            op(op(b, inv(a)), a) = op(b, e)
            [by rewrite inva-a assoc-step]
          @id-right |
            forall g: G; op(g, e) = g
            [by axiom identityRight]
          @b-e |
            op(b, e) = b
            [by forall_elim(b) id-right]
          @conclusion-inner |
            op(op(b, inv(a)), a) = b
            [by rewrite b-e with-e]
        }
      @close-b |
        forall b: G; op(op(b, inv(a)), a) = b
        [by forall_intro generalize-b]
    }
  @conclusion |
    forall a, b: G; op(op(b, inv(a)), a) = b
    [by forall_intro generalize-a]
qed
```

**Uniqueness** — any two solutions coincide, by right cancellation:

```bpa
theorem solutionUnique: forall a, b, x, y: G;
  op(x, a) = b -> op(y, a) = b -> x = y
proof
  @generalize-a |
    fix a: G {
      @generalize-b |
        fix b: G {
          @generalize-x |
            fix x: G {
              @generalize-y |
                fix y: G {
                  @given-x |
                    assume op(x, a) = b {
                      @given-y |
                        assume op(y, a) = b {
                          @xa-b |
                            op(x, a) = b
                            [by hypothesis given-x]
                          @ya-b |
                            op(y, a) = b
                            [by hypothesis given-y]
                          @b-ya |
                            b = op(y, a)
                            [by symmetry ya-b]
                          @xa-ya |
                            op(x, a) = op(y, a)
                            [by rewrite b-ya xa-b]
                          @cancel-r |
                            forall aa, bb, cc: G; op(bb, aa) = op(cc, aa) -> bb = cc
                            [by theorem cancelRight]
                          @cr-at |
                            op(x, a) = op(y, a) -> x = y
                            [by forall_elim(a, x, y) cancel-r]
                          @x-is-y |
                            x = y
                            [by modus_ponens cr-at xa-ya]
                        }
                      @disch-y |
                        op(y, a) = b -> x = y
                        [by implies_intro given-y]
                    }
                  @disch-x |
                    op(x, a) = b -> op(y, a) = b -> x = y
                    [by implies_intro given-x]
                }
              @close-y |
                forall y: G; op(x, a) = b -> op(y, a) = b -> x = y
                [by forall_intro generalize-y]
            }
          @close-x |
            forall x, y: G; op(x, a) = b -> op(y, a) = b -> x = y
            [by forall_intro generalize-x]
        }
      @close-b |
        forall b, x, y: G; op(x, a) = b -> op(y, a) = b -> x = y
        [by forall_intro generalize-b]
    }
  @conclusion |
    forall a, b, x, y: G; op(x, a) = b -> op(y, a) = b -> x = y
    [by forall_intro generalize-a]
qed
```

## Exercise 31 — $a^2 = e$ for all $a$ implies $G$ abelian

> Show that if $a^2 = e$ for all elements $a$ in a group $G$, then $G$ must be
> abelian.

#### Solution

If every element squares to `e`, then every element is its own inverse
(`inverseUnique`); combined with $(ab)^{-1} = b^{-1}a^{-1}$ this gives
$ab = (ab)^{-1} = b^{-1}a^{-1} = ba$.

```bpa
theorem selfInverse: (forall a: G; op(a, a) = e) -> forall a: G; inv(a) = a
proof
  @given |
    assume forall a: G; op(a, a) = e {
      @sq |
        forall a: G; op(a, a) = e
        [by hypothesis given]
      @generalize-a |
        fix a: G {
          @aa-is-e |
            op(a, a) = e
            [by forall_elim(a) sq]
          @inv-unique |
            forall x, y: G; op(x, y) = e -> y = inv(x)
            [by theorem inverseUnique]
          @at |
            op(a, a) = e -> a = inv(a)
            [by forall_elim(a, a) inv-unique]
          @a-is-inva |
            a = inv(a)
            [by modus_ponens at aa-is-e]
          @inva-is-a |
            inv(a) = a
            [by symmetry a-is-inva]
        }
      @discharge-inner |
        forall a: G; inv(a) = a
        [by forall_intro generalize-a]
    }
  @conclusion |
    (forall a: G; op(a, a) = e) -> forall a: G; inv(a) = a
    [by implies_intro given]
qed

theorem squareIdImpliesAbelian:
  (forall a: G; op(a, a) = e) -> forall x, y: G; op(x, y) = op(y, x)
proof
  @given |
    assume forall a: G; op(a, a) = e {
      @sq |
        forall a: G; op(a, a) = e
        [by hypothesis given]
      @self-inv-thm |
        (forall a: G; op(a, a) = e) -> forall a: G; inv(a) = a
        [by theorem selfInverse]
      @self-inv |
        forall a: G; inv(a) = a
        [by modus_ponens self-inv-thm sq]
      @generalize-x |
        fix x: G {
          @generalize-y |
            fix y: G {
              @inv-prod-thm |
                forall a, b: G; inv(op(a, b)) = op(inv(b), inv(a))
                [by theorem invProduct]
              @inv-xy |
                inv(op(x, y)) = op(inv(y), inv(x))
                [by forall_elim(x, y) inv-prod-thm]
              @inv-x |
                inv(x) = x
                [by forall_elim(x) self-inv]
              @inv-y |
                inv(y) = y
                [by forall_elim(y) self-inv]
              @inv-xy-self |
                inv(op(x, y)) = op(x, y)
                [by forall_elim(op(x, y)) self-inv]
              @step1 |
                inv(op(x, y)) = op(y, inv(x))
                [by rewrite inv-y inv-xy]
              @step2 |
                inv(op(x, y)) = op(y, x)
                [by rewrite inv-x step1]
              @xy-is-inv |
                op(x, y) = inv(op(x, y))
                [by symmetry inv-xy-self]
              @xy-is-yx |
                op(x, y) = op(y, x)
                [by rewrite step2 xy-is-inv]
            }
          @close-y |
            forall y: G; op(x, y) = op(y, x)
            [by forall_intro generalize-y]
        }
      @discharge-inner |
        forall x, y: G; op(x, y) = op(y, x)
        [by forall_intro generalize-x]
    }
  @conclusion |
    (forall a: G; op(a, a) = e) -> forall x, y: G; op(x, y) = op(y, x)
    [by implies_intro given]
qed
```

## Exercises requiring machinery bpa does not yet have

These are honest markers — each names the standard-library construction it would
need. They are the backlog that future AATA chapters will motivate.

- **Exercises 1, 6, 19–24** (compute in $\mathbb{Z}_n$ / $U(n)$; identities,
  associativity, distributivity of modular arithmetic).
  #### Solution
  Not solvable without a concrete $\mathbb{Z}_n$ model (integers modulo $n$ as a
  sort with its operations) — bpa has Peano naturals and `mod`, but not the
  quotient structure $\mathbb{Z}/n\mathbb{Z}$ as a group.
- **Exercises 2–5** (Cayley tables; symmetries of the rectangle, rhombus,
  square).
  #### Solution
  Not solvable without finite sets and an explicit enumeration of group elements
  (a finite carrier with a tabulated operation).
- **Exercises 7–15** (specific groups: $\mathbb{R}^*$, $SL_2$, the Heisenberg
  group, matrix determinants, $\mathbb{R}^* \times \mathbb{Z}$).
  #### Solution
  Not solvable without the relevant carrier constructions (real numbers, the
  matrix / $GL_n$ construction, direct products) — none of which bpa has.
- **Exercises 17, 18** (count groups of order 8; $n!$ permutations).
  #### Solution
  Not solvable without finite sets + cardinality/counting.
- **Exercises 25, 27, 29** ($ab^n a^{-1} = (aba^{-1})^n$; product of inverses;
  exponent laws — all indexed by $n \in \mathbb{Z}$).
  #### Solution
  Expressible via induction over a Nat exponent (bpa's `std/peano` `induction`),
  but they require defining $g^n$ (group power) as a recursive function — a small
  addition to `std/group.bpa`, deferred to a later pass rather than done here.
