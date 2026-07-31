# Sets

A literate `bpa` transliteration of **Chapter 1 ("Preliminaries"), §1.2.1
"Set Theory"** of Thomas W. Judson's *Abstract Algebra: Theory and
Applications* (source: `vendor/aata/src/sets.xml`; © 1997–2026 Judson,
GFDL 1.3). The book's prose is reproduced in order; each result the book states
is followed by a machine-checked `bpa` proof. Run `bpa check aata/sets.md` to
verify every proof block below.

The theory of sets lives in `std/set.bpa`: a sort `Universe` of elements, a sort
`Set`, the operations `union` / `intersection` / `difference` / `complement`,
the empty set `emptyset`, a membership predicate `member`, and axioms fixing
each operation *membershipwise* together with **extensionality**. We import it
and keep the library names.

```bpa
import set <<< "std/set.bpa"

sort Universe = set.Universe
sort Set = set.Set
const emptyset = set.emptyset
func union = set.union
func intersection = set.intersection
func difference = set.difference
func complement = set.complement
pred member = set.member
axiom unionMember = set.unionMember
axiom intersectionMember = set.intersectionMember
axiom differenceMember = set.differenceMember
axiom complementMember = set.complementMember
axiom emptysetMember = set.emptysetMember
axiom extensional = set.extensionality
```

> *§1.1 "A Short Note on Proofs" and §1.1.1 "Some Cautions and Suggestions"
> are expository remarks on mathematical writing — statements, quantifiers,
> converses, contrapositives, proof by contradiction and induction — with no
> formal results to transcribe. They are omitted here; see the book.*

## Set Theory

A **set** is a well-defined collection of objects; that is, it is defined in
such a manner that we can determine for any given object $x$ whether or not $x$
belongs to the set. The objects that belong to a set are called its **elements**
or **members**. We will denote sets by capital letters, such as $A$ or $X$; if
$a$ is an element of the set $A$, we write $a \in A$.

A set is usually specified either by listing all of its elements inside a pair
of braces or by stating the property that determines whether or not an object
$x$ belongs to the set. We might write

$$X = \{ x_1, x_2, \ldots, x_n \}$$

for a set containing elements $x_1, x_2, \ldots, x_n$, or

$$X = \{ x : x \text{ satisfies } \mathcal{P} \}$$

if each $x$ in $X$ satisfies a certain property $\mathcal{P}$. For example, if
$E$ is the set of even positive integers, we can describe $E$ by writing either
$E = \{2, 4, 6, \ldots\}$ or $E = \{ x : x \text{ is an even integer and } x > 0 \}$.
We write $2 \in E$ when we want to say that 2 is in the set $E$, and
$-3 \notin E$ to say that $-3$ is not in the set $E$.

Some of the more important sets that we will consider are the following:

$$\mathbb{N} = \{n : n \text{ is a natural number}\} = \{1, 2, 3, \ldots\};$$
$$\mathbb{Z} = \{n : n \text{ is an integer}\} = \{\ldots, -1, 0, 1, 2, \ldots\};$$
$$\mathbb{Q} = \{r : r \text{ is a rational number}\} = \{p/q : p, q \in \mathbb{Z} \text{ where } q \neq 0\};$$
$$\mathbb{R} = \{ x : x \text{ is a real number} \};$$
$$\mathbb{C} = \{z : z \text{ is a complex number}\}.$$

> *These concrete number systems ($\mathbb{N}, \mathbb{Z}, \mathbb{Q},
> \mathbb{R}, \mathbb{C}$) are named for context. `std/set.bpa` works over an
> abstract sort `Universe` of elements — it does not fix any particular one — so
> the identities below hold for sets drawn from **any** universe.*

We can find various relations between sets as well as perform operations on
sets. A set $A$ is a **subset** of $B$, written $A \subset B$ or $B \supset A$,
if every element of $A$ is also an element of $B$. For example,
$\{4,5,8\} \subset \{2,3,4,5,6,7,8,9\}$ and
$\mathbb{N} \subset \mathbb{Z} \subset \mathbb{Q} \subset \mathbb{R} \subset \mathbb{C}$.
Trivially, every set is a subset of itself. A set $B$ is a **proper subset** of a
set $A$ if $B \subset A$ but $B \neq A$. If $A$ is not a subset of $B$, we write
$A \not\subset B$; for example, $\{4,7,9\} \not\subset \{2,4,5,8,9\}$. Two sets
are **equal**, written $A = B$, if we can show that $A \subset B$ and
$B \subset A$.

> *This last sentence is exactly the **extensionality** axiom that drives every
> proof in this file: to prove `A = B`, prove each of the two inclusions
> `member(x, A) -> member(x, B)` and `member(x, B) -> member(x, A)`.*

It is convenient to have a set with no elements in it. This set is called the
**empty set** and is denoted by $\emptyset$. Note that the empty set is a subset
of every set.

To construct new sets out of old sets, we can perform certain operations: the
**union** $A \cup B$ of two sets $A$ and $B$ is defined as

$$A \cup B = \{x : x \in A \text{ or } x \in B \};$$

the **intersection** of $A$ and $B$ is defined by

$$A \cap B = \{x : x \in A \text{ and } x \in B \}.$$

If $A = \{1,3,5\}$ and $B = \{1,2,3,9\}$, then $A \cup B = \{1,2,3,5,9\}$ and
$A \cap B = \{1,3\}$. We can consider the union and the intersection of more than
two sets. In this case we write

$$\bigcup_{i=1}^{n} A_i = A_1 \cup \cdots \cup A_n \quad\text{and}\quad \bigcap_{i=1}^{n} A_i = A_1 \cap \cdots \cap A_n$$

for the union and intersection, respectively, of the sets $A_1, \ldots, A_n$.

> *`bpa` cannot currently encode the indexed families $\bigcup_{i=1}^{n} A_i$ /
> $\bigcap_{i=1}^{n} A_i$: they range over a variable number $n$ of sets, which
> would need a sort of finite sequences of `Set` (or a set-of-sets) that this
> theory does not model.*

When two sets have no elements in common, they are said to be **disjoint**; for
example, if $E$ is the set of even integers and $O$ is the set of odd integers,
then $E$ and $O$ are disjoint. Two sets $A$ and $B$ are disjoint exactly when
$A \cap B = \emptyset$.

Sometimes we will work within one fixed set $U$, called the **universal set**.
For any set $A \subset U$, we define the **complement** of $A$, denoted by $A'$,
to be the set

$$A' = \{ x : x \in U \text{ and } x \notin A \}.$$

> *`std/set.bpa` fixes `complement` directly by its membership rule
> `member(x, complement(a)) <-> not member(x, a)` (written, since `bpa` has no
> `<->`, as two implications in `complementMember`). This is the same object as
> the book's $A'$ **without** introducing an explicit universal-set constant $U$:
> the ambient `Universe` sort already plays the role of $U$, and no theorem below
> needs $U$ as a first-class set.*

We define the **difference** of two sets $A$ and $B$ to be

$$A \setminus B = A \cap B' = \{ x : x \in A \text{ and } x \notin B \}.$$

**Example.** Let $\mathbb{R}$ be the universal set and suppose that

$$A = \{ x \in \mathbb{R} : 0 < x \leq 3 \} \quad\text{and}\quad B = \{ x \in \mathbb{R} : 2 \leq x < 4 \}.$$

Then

$$A \cap B = \{ x \in \mathbb{R} : 2 \leq x \leq 3 \}, \quad A \cup B = \{ x \in \mathbb{R} : 0 < x < 4 \},$$
$$A \setminus B = \{ x \in \mathbb{R} : 0 < x < 2 \}, \quad A' = \{ x \in \mathbb{R} : x \leq 0 \text{ or } x > 3 \}.$$

> *A concrete numeric illustration over $\mathbb{R}$; nothing to formalize (the
> abstract theory has no order or real-number structure). It is reproduced for
> completeness.*

## Proposition

> Let $A$, $B$, and $C$ be sets. Then
>
> 1. $A \cup A = A$, $A \cap A = A$, and $A \setminus A = \emptyset$;
> 2. $A \cup \emptyset = A$ and $A \cap \emptyset = \emptyset$;
> 3. $A \cup (B \cup C) = (A \cup B) \cup C$ and $A \cap (B \cap C) = (A \cap B) \cap C$;
> 4. $A \cup B = B \cup A$ and $A \cap B = B \cap A$;
> 5. $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$;
> 6. $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$.

The book proves (1) and (3) and leaves the rest to the exercises; here we prove
**all six**. Each identity follows the same recipe: by extensionality it
suffices to prove the two inclusions; `fix` an element, unfold `member(x, ·)`
on every compound subterm via its defining axiom, and discharge the resulting
purely propositional goal with a single `[by tautology ...]`. The forward and
backward inclusions use different element names (`x` and `y`) so that closing
the second with `forall_intro` does not trip the eigenvariable escape check on
the first.

**(1)** Union and intersection are *idempotent* — after unfolding,
`member(x,a) or member(x,a)` and `member(x,a) and member(x,a)` are both just
`member(x,a)` — and the *self-difference* `A \ A` is empty, because
`member(x, difference(a,a))` unfolds to the contradiction
`member(x,a) and (not member(x,a))` while nothing belongs to `emptyset`.

```bpa
theorem unionIdempotent: forall a: Set; union(a, a) = a
proof
  @gen-a |
    fix a: Set {
      @ax-union |
        forall p, q: Set; forall x: Universe;
          (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
          and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
        [by axiom unionMember]
      @mem-union_a-a |
        forall x: Universe;
          (member(x, union(a, a)) -> (member(x, a) or member(x, a)))
          and ((member(x, a) or member(x, a)) -> member(x, union(a, a)))
        [by forall_elim(a, a) ax-union]
      @fwd |
        fix x: Universe {
          @fwd-union_a-a |
            (member(x, union(a, a)) -> (member(x, a) or member(x, a)))
            and ((member(x, a) or member(x, a)) -> member(x, union(a, a)))
            [by forall_elim(x) mem-union_a-a]
          @fwd-assume |
            assume member(x, union(a, a)) {
              @fwd-hyp |
                member(x, union(a, a))
                [by hypothesis fwd-assume]
              @fwd-concl |
                member(x, a)
                [by tautology fwd-union_a-a fwd-hyp]
            }
          @fwd-imp |
            member(x, union(a, a)) -> member(x, a)
            [by implies_intro fwd-assume]
        }
      @fwd-all |
        forall x: Universe; member(x, union(a, a)) -> member(x, a)
        [by forall_intro fwd]
      @bwd |
        fix y: Universe {
          @bwd-union_a-a |
            (member(y, union(a, a)) -> (member(y, a) or member(y, a)))
            and ((member(y, a) or member(y, a)) -> member(y, union(a, a)))
            [by forall_elim(y) mem-union_a-a]
          @bwd-assume |
            assume member(y, a) {
              @bwd-hyp |
                member(y, a)
                [by hypothesis bwd-assume]
              @bwd-concl |
                member(y, union(a, a))
                [by tautology bwd-union_a-a bwd-hyp]
            }
          @bwd-imp |
            member(y, a) -> member(y, union(a, a))
            [by implies_intro bwd-assume]
        }
      @bwd-all |
        forall y: Universe; member(y, a) -> member(y, union(a, a))
        [by forall_intro bwd]
      @ext |
        forall p, q: Set;
          (forall x: Universe; member(x, p) -> member(x, q)) ->
          (forall x: Universe; member(x, q) -> member(x, p)) ->
          p = q
        [by axiom extensional]
      @ext-at |
        (forall x: Universe; member(x, union(a, a)) -> member(x, a)) ->
        (forall x: Universe; member(x, a) -> member(x, union(a, a))) ->
        union(a, a) = a
        [by forall_elim(union(a, a), a) ext]
      @step1 |
        (forall x: Universe; member(x, a) -> member(x, union(a, a))) ->
        union(a, a) = a
        [by modus_ponens ext-at fwd-all]
      @done |
        union(a, a) = a
        [by modus_ponens step1 bwd-all]
    }
  @close-a |
    forall a: Set; union(a, a) = a
    [by forall_intro gen-a]
qed
```

```bpa
theorem intersectionIdempotent: forall a: Set; intersection(a, a) = a
proof
  @gen-a |
    fix a: Set {
      @ax-intersection |
        forall p, q: Set; forall x: Universe;
          (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
          and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
        [by axiom intersectionMember]
      @mem-intersection_a-a |
        forall x: Universe;
          (member(x, intersection(a, a)) -> (member(x, a) and member(x, a)))
          and ((member(x, a) and member(x, a)) -> member(x, intersection(a, a)))
        [by forall_elim(a, a) ax-intersection]
      @fwd |
        fix x: Universe {
          @fwd-intersection_a-a |
            (member(x, intersection(a, a)) -> (member(x, a) and member(x, a)))
            and ((member(x, a) and member(x, a)) -> member(x, intersection(a, a)))
            [by forall_elim(x) mem-intersection_a-a]
          @fwd-assume |
            assume member(x, intersection(a, a)) {
              @fwd-hyp |
                member(x, intersection(a, a))
                [by hypothesis fwd-assume]
              @fwd-concl |
                member(x, a)
                [by tautology fwd-intersection_a-a fwd-hyp]
            }
          @fwd-imp |
            member(x, intersection(a, a)) -> member(x, a)
            [by implies_intro fwd-assume]
        }
      @fwd-all |
        forall x: Universe; member(x, intersection(a, a)) -> member(x, a)
        [by forall_intro fwd]
      @bwd |
        fix y: Universe {
          @bwd-intersection_a-a |
            (member(y, intersection(a, a)) -> (member(y, a) and member(y, a)))
            and ((member(y, a) and member(y, a)) -> member(y, intersection(a, a)))
            [by forall_elim(y) mem-intersection_a-a]
          @bwd-assume |
            assume member(y, a) {
              @bwd-hyp |
                member(y, a)
                [by hypothesis bwd-assume]
              @bwd-concl |
                member(y, intersection(a, a))
                [by tautology bwd-intersection_a-a bwd-hyp]
            }
          @bwd-imp |
            member(y, a) -> member(y, intersection(a, a))
            [by implies_intro bwd-assume]
        }
      @bwd-all |
        forall y: Universe; member(y, a) -> member(y, intersection(a, a))
        [by forall_intro bwd]
      @ext |
        forall p, q: Set;
          (forall x: Universe; member(x, p) -> member(x, q)) ->
          (forall x: Universe; member(x, q) -> member(x, p)) ->
          p = q
        [by axiom extensional]
      @ext-at |
        (forall x: Universe; member(x, intersection(a, a)) -> member(x, a)) ->
        (forall x: Universe; member(x, a) -> member(x, intersection(a, a))) ->
        intersection(a, a) = a
        [by forall_elim(intersection(a, a), a) ext]
      @step1 |
        (forall x: Universe; member(x, a) -> member(x, intersection(a, a))) ->
        intersection(a, a) = a
        [by modus_ponens ext-at fwd-all]
      @done |
        intersection(a, a) = a
        [by modus_ponens step1 bwd-all]
    }
  @close-a |
    forall a: Set; intersection(a, a) = a
    [by forall_intro gen-a]
qed
```

```bpa
theorem differenceSelf: forall a: Set; difference(a, a) = emptyset
proof
  @gen-a |
    fix a: Set {
      @ax-difference |
        forall p, q: Set; forall x: Universe;
          (member(x, difference(p, q)) -> (member(x, p) and (not member(x, q))))
          and ((member(x, p) and (not member(x, q))) -> member(x, difference(p, q)))
        [by axiom differenceMember]
      @mem-difference_a-a |
        forall x: Universe;
          (member(x, difference(a, a)) -> (member(x, a) and (not member(x, a))))
          and ((member(x, a) and (not member(x, a))) -> member(x, difference(a, a)))
        [by forall_elim(a, a) ax-difference]
      @ax-empty |
        forall x: Universe; not member(x, emptyset)
        [by axiom emptysetMember]
      @fwd |
        fix x: Universe {
          @fwd-difference_a-a |
            (member(x, difference(a, a)) -> (member(x, a) and (not member(x, a))))
            and ((member(x, a) and (not member(x, a))) -> member(x, difference(a, a)))
            [by forall_elim(x) mem-difference_a-a]
          @fwd-empty |
            not member(x, emptyset)
            [by forall_elim(x) ax-empty]
          @fwd-assume |
            assume member(x, difference(a, a)) {
              @fwd-hyp |
                member(x, difference(a, a))
                [by hypothesis fwd-assume]
              @fwd-concl |
                member(x, emptyset)
                [by tautology fwd-difference_a-a fwd-empty fwd-hyp]
            }
          @fwd-imp |
            member(x, difference(a, a)) -> member(x, emptyset)
            [by implies_intro fwd-assume]
        }
      @fwd-all |
        forall x: Universe; member(x, difference(a, a)) -> member(x, emptyset)
        [by forall_intro fwd]
      @bwd |
        fix y: Universe {
          @bwd-difference_a-a |
            (member(y, difference(a, a)) -> (member(y, a) and (not member(y, a))))
            and ((member(y, a) and (not member(y, a))) -> member(y, difference(a, a)))
            [by forall_elim(y) mem-difference_a-a]
          @bwd-empty |
            not member(y, emptyset)
            [by forall_elim(y) ax-empty]
          @bwd-assume |
            assume member(y, emptyset) {
              @bwd-hyp |
                member(y, emptyset)
                [by hypothesis bwd-assume]
              @bwd-concl |
                member(y, difference(a, a))
                [by tautology bwd-difference_a-a bwd-empty bwd-hyp]
            }
          @bwd-imp |
            member(y, emptyset) -> member(y, difference(a, a))
            [by implies_intro bwd-assume]
        }
      @bwd-all |
        forall y: Universe; member(y, emptyset) -> member(y, difference(a, a))
        [by forall_intro bwd]
      @ext |
        forall p, q: Set;
          (forall x: Universe; member(x, p) -> member(x, q)) ->
          (forall x: Universe; member(x, q) -> member(x, p)) ->
          p = q
        [by axiom extensional]
      @ext-at |
        (forall x: Universe; member(x, difference(a, a)) -> member(x, emptyset)) ->
        (forall x: Universe; member(x, emptyset) -> member(x, difference(a, a))) ->
        difference(a, a) = emptyset
        [by forall_elim(difference(a, a), emptyset) ext]
      @step1 |
        (forall x: Universe; member(x, emptyset) -> member(x, difference(a, a))) ->
        difference(a, a) = emptyset
        [by modus_ponens ext-at fwd-all]
      @done |
        difference(a, a) = emptyset
        [by modus_ponens step1 bwd-all]
    }
  @close-a |
    forall a: Set; difference(a, a) = emptyset
    [by forall_intro gen-a]
qed
```

**(2)** The empty set is the *identity* for union and an *annihilator* for
intersection: `member(x, emptyset)` is always false (`emptysetMember`), so a
trailing `or member(x, emptyset)` drops and a trailing `and member(x, emptyset)`
forces falsehood.

```bpa
theorem unionEmpty: forall a: Set; union(a, emptyset) = a
proof
  @gen-a |
    fix a: Set {
      @ax-union |
        forall p, q: Set; forall x: Universe;
          (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
          and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
        [by axiom unionMember]
      @mem-union_a-emptyset |
        forall x: Universe;
          (member(x, union(a, emptyset)) -> (member(x, a) or member(x, emptyset)))
          and ((member(x, a) or member(x, emptyset)) -> member(x, union(a, emptyset)))
        [by forall_elim(a, emptyset) ax-union]
      @ax-empty |
        forall x: Universe; not member(x, emptyset)
        [by axiom emptysetMember]
      @fwd |
        fix x: Universe {
          @fwd-union_a-emptyset |
            (member(x, union(a, emptyset)) -> (member(x, a) or member(x, emptyset)))
            and ((member(x, a) or member(x, emptyset)) -> member(x, union(a, emptyset)))
            [by forall_elim(x) mem-union_a-emptyset]
          @fwd-empty |
            not member(x, emptyset)
            [by forall_elim(x) ax-empty]
          @fwd-assume |
            assume member(x, union(a, emptyset)) {
              @fwd-hyp |
                member(x, union(a, emptyset))
                [by hypothesis fwd-assume]
              @fwd-concl |
                member(x, a)
                [by tautology fwd-union_a-emptyset fwd-empty fwd-hyp]
            }
          @fwd-imp |
            member(x, union(a, emptyset)) -> member(x, a)
            [by implies_intro fwd-assume]
        }
      @fwd-all |
        forall x: Universe; member(x, union(a, emptyset)) -> member(x, a)
        [by forall_intro fwd]
      @bwd |
        fix y: Universe {
          @bwd-union_a-emptyset |
            (member(y, union(a, emptyset)) -> (member(y, a) or member(y, emptyset)))
            and ((member(y, a) or member(y, emptyset)) -> member(y, union(a, emptyset)))
            [by forall_elim(y) mem-union_a-emptyset]
          @bwd-empty |
            not member(y, emptyset)
            [by forall_elim(y) ax-empty]
          @bwd-assume |
            assume member(y, a) {
              @bwd-hyp |
                member(y, a)
                [by hypothesis bwd-assume]
              @bwd-concl |
                member(y, union(a, emptyset))
                [by tautology bwd-union_a-emptyset bwd-empty bwd-hyp]
            }
          @bwd-imp |
            member(y, a) -> member(y, union(a, emptyset))
            [by implies_intro bwd-assume]
        }
      @bwd-all |
        forall y: Universe; member(y, a) -> member(y, union(a, emptyset))
        [by forall_intro bwd]
      @ext |
        forall p, q: Set;
          (forall x: Universe; member(x, p) -> member(x, q)) ->
          (forall x: Universe; member(x, q) -> member(x, p)) ->
          p = q
        [by axiom extensional]
      @ext-at |
        (forall x: Universe; member(x, union(a, emptyset)) -> member(x, a)) ->
        (forall x: Universe; member(x, a) -> member(x, union(a, emptyset))) ->
        union(a, emptyset) = a
        [by forall_elim(union(a, emptyset), a) ext]
      @step1 |
        (forall x: Universe; member(x, a) -> member(x, union(a, emptyset))) ->
        union(a, emptyset) = a
        [by modus_ponens ext-at fwd-all]
      @done |
        union(a, emptyset) = a
        [by modus_ponens step1 bwd-all]
    }
  @close-a |
    forall a: Set; union(a, emptyset) = a
    [by forall_intro gen-a]
qed
```

```bpa
theorem intersectionEmpty: forall a: Set; intersection(a, emptyset) = emptyset
proof
  @gen-a |
    fix a: Set {
      @ax-intersection |
        forall p, q: Set; forall x: Universe;
          (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
          and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
        [by axiom intersectionMember]
      @mem-intersection_a-emptyset |
        forall x: Universe;
          (member(x, intersection(a, emptyset)) -> (member(x, a) and member(x, emptyset)))
          and ((member(x, a) and member(x, emptyset)) -> member(x, intersection(a, emptyset)))
        [by forall_elim(a, emptyset) ax-intersection]
      @ax-empty |
        forall x: Universe; not member(x, emptyset)
        [by axiom emptysetMember]
      @fwd |
        fix x: Universe {
          @fwd-intersection_a-emptyset |
            (member(x, intersection(a, emptyset)) -> (member(x, a) and member(x, emptyset)))
            and ((member(x, a) and member(x, emptyset)) -> member(x, intersection(a, emptyset)))
            [by forall_elim(x) mem-intersection_a-emptyset]
          @fwd-empty |
            not member(x, emptyset)
            [by forall_elim(x) ax-empty]
          @fwd-assume |
            assume member(x, intersection(a, emptyset)) {
              @fwd-hyp |
                member(x, intersection(a, emptyset))
                [by hypothesis fwd-assume]
              @fwd-concl |
                member(x, emptyset)
                [by tautology fwd-intersection_a-emptyset fwd-empty fwd-hyp]
            }
          @fwd-imp |
            member(x, intersection(a, emptyset)) -> member(x, emptyset)
            [by implies_intro fwd-assume]
        }
      @fwd-all |
        forall x: Universe; member(x, intersection(a, emptyset)) -> member(x, emptyset)
        [by forall_intro fwd]
      @bwd |
        fix y: Universe {
          @bwd-intersection_a-emptyset |
            (member(y, intersection(a, emptyset)) -> (member(y, a) and member(y, emptyset)))
            and ((member(y, a) and member(y, emptyset)) -> member(y, intersection(a, emptyset)))
            [by forall_elim(y) mem-intersection_a-emptyset]
          @bwd-empty |
            not member(y, emptyset)
            [by forall_elim(y) ax-empty]
          @bwd-assume |
            assume member(y, emptyset) {
              @bwd-hyp |
                member(y, emptyset)
                [by hypothesis bwd-assume]
              @bwd-concl |
                member(y, intersection(a, emptyset))
                [by tautology bwd-intersection_a-emptyset bwd-empty bwd-hyp]
            }
          @bwd-imp |
            member(y, emptyset) -> member(y, intersection(a, emptyset))
            [by implies_intro bwd-assume]
        }
      @bwd-all |
        forall y: Universe; member(y, emptyset) -> member(y, intersection(a, emptyset))
        [by forall_intro bwd]
      @ext |
        forall p, q: Set;
          (forall x: Universe; member(x, p) -> member(x, q)) ->
          (forall x: Universe; member(x, q) -> member(x, p)) ->
          p = q
        [by axiom extensional]
      @ext-at |
        (forall x: Universe; member(x, intersection(a, emptyset)) -> member(x, emptyset)) ->
        (forall x: Universe; member(x, emptyset) -> member(x, intersection(a, emptyset))) ->
        intersection(a, emptyset) = emptyset
        [by forall_elim(intersection(a, emptyset), emptyset) ext]
      @step1 |
        (forall x: Universe; member(x, emptyset) -> member(x, intersection(a, emptyset))) ->
        intersection(a, emptyset) = emptyset
        [by modus_ponens ext-at fwd-all]
      @done |
        intersection(a, emptyset) = emptyset
        [by modus_ponens step1 bwd-all]
    }
  @close-a |
    forall a: Set; intersection(a, emptyset) = emptyset
    [by forall_intro gen-a]
qed
```

**(3)** Both operations are *associative* — after unfolding, this is the
propositional associativity of `or` (resp. `and`) over the three atoms
`member(x,a)`, `member(x,b)`, `member(x,c)`.

```bpa
theorem unionAssociative: forall a, b, c: Set; union(a, union(b, c)) = union(union(a, b), c)
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @gen-c |
            fix c: Set {
              @ax-union |
                forall p, q: Set; forall x: Universe;
                  (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
                  and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
                [by axiom unionMember]
              @mem-union_b-c |
                forall x: Universe;
                  (member(x, union(b, c)) -> (member(x, b) or member(x, c)))
                  and ((member(x, b) or member(x, c)) -> member(x, union(b, c)))
                [by forall_elim(b, c) ax-union]
              @mem-union_a-union_b-c |
                forall x: Universe;
                  (member(x, union(a, union(b, c))) -> (member(x, a) or member(x, union(b, c))))
                  and ((member(x, a) or member(x, union(b, c))) -> member(x, union(a, union(b, c))))
                [by forall_elim(a, union(b, c)) ax-union]
              @mem-union_a-b |
                forall x: Universe;
                  (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
                  and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
                [by forall_elim(a, b) ax-union]
              @mem-union_union_a-b-c |
                forall x: Universe;
                  (member(x, union(union(a, b), c)) -> (member(x, union(a, b)) or member(x, c)))
                  and ((member(x, union(a, b)) or member(x, c)) -> member(x, union(union(a, b), c)))
                [by forall_elim(union(a, b), c) ax-union]
              @fwd |
                fix x: Universe {
                  @fwd-union_b-c |
                    (member(x, union(b, c)) -> (member(x, b) or member(x, c)))
                    and ((member(x, b) or member(x, c)) -> member(x, union(b, c)))
                    [by forall_elim(x) mem-union_b-c]
                  @fwd-union_a-union_b-c |
                    (member(x, union(a, union(b, c))) -> (member(x, a) or member(x, union(b, c))))
                    and ((member(x, a) or member(x, union(b, c))) -> member(x, union(a, union(b, c))))
                    [by forall_elim(x) mem-union_a-union_b-c]
                  @fwd-union_a-b |
                    (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
                    and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
                    [by forall_elim(x) mem-union_a-b]
                  @fwd-union_union_a-b-c |
                    (member(x, union(union(a, b), c)) -> (member(x, union(a, b)) or member(x, c)))
                    and ((member(x, union(a, b)) or member(x, c)) -> member(x, union(union(a, b), c)))
                    [by forall_elim(x) mem-union_union_a-b-c]
                  @fwd-assume |
                    assume member(x, union(a, union(b, c))) {
                      @fwd-hyp |
                        member(x, union(a, union(b, c)))
                        [by hypothesis fwd-assume]
                      @fwd-concl |
                        member(x, union(union(a, b), c))
                        [by tautology fwd-union_b-c fwd-union_a-union_b-c fwd-union_a-b fwd-union_union_a-b-c fwd-hyp]
                    }
                  @fwd-imp |
                    member(x, union(a, union(b, c))) -> member(x, union(union(a, b), c))
                    [by implies_intro fwd-assume]
                }
              @fwd-all |
                forall x: Universe; member(x, union(a, union(b, c))) -> member(x, union(union(a, b), c))
                [by forall_intro fwd]
              @bwd |
                fix y: Universe {
                  @bwd-union_b-c |
                    (member(y, union(b, c)) -> (member(y, b) or member(y, c)))
                    and ((member(y, b) or member(y, c)) -> member(y, union(b, c)))
                    [by forall_elim(y) mem-union_b-c]
                  @bwd-union_a-union_b-c |
                    (member(y, union(a, union(b, c))) -> (member(y, a) or member(y, union(b, c))))
                    and ((member(y, a) or member(y, union(b, c))) -> member(y, union(a, union(b, c))))
                    [by forall_elim(y) mem-union_a-union_b-c]
                  @bwd-union_a-b |
                    (member(y, union(a, b)) -> (member(y, a) or member(y, b)))
                    and ((member(y, a) or member(y, b)) -> member(y, union(a, b)))
                    [by forall_elim(y) mem-union_a-b]
                  @bwd-union_union_a-b-c |
                    (member(y, union(union(a, b), c)) -> (member(y, union(a, b)) or member(y, c)))
                    and ((member(y, union(a, b)) or member(y, c)) -> member(y, union(union(a, b), c)))
                    [by forall_elim(y) mem-union_union_a-b-c]
                  @bwd-assume |
                    assume member(y, union(union(a, b), c)) {
                      @bwd-hyp |
                        member(y, union(union(a, b), c))
                        [by hypothesis bwd-assume]
                      @bwd-concl |
                        member(y, union(a, union(b, c)))
                        [by tautology bwd-union_b-c bwd-union_a-union_b-c bwd-union_a-b bwd-union_union_a-b-c bwd-hyp]
                    }
                  @bwd-imp |
                    member(y, union(union(a, b), c)) -> member(y, union(a, union(b, c)))
                    [by implies_intro bwd-assume]
                }
              @bwd-all |
                forall y: Universe; member(y, union(union(a, b), c)) -> member(y, union(a, union(b, c)))
                [by forall_intro bwd]
              @ext |
                forall p, q: Set;
                  (forall x: Universe; member(x, p) -> member(x, q)) ->
                  (forall x: Universe; member(x, q) -> member(x, p)) ->
                  p = q
                [by axiom extensional]
              @ext-at |
                (forall x: Universe; member(x, union(a, union(b, c))) -> member(x, union(union(a, b), c))) ->
                (forall x: Universe; member(x, union(union(a, b), c)) -> member(x, union(a, union(b, c)))) ->
                union(a, union(b, c)) = union(union(a, b), c)
                [by forall_elim(union(a, union(b, c)), union(union(a, b), c)) ext]
              @step1 |
                (forall x: Universe; member(x, union(union(a, b), c)) -> member(x, union(a, union(b, c)))) ->
                union(a, union(b, c)) = union(union(a, b), c)
                [by modus_ponens ext-at fwd-all]
              @done |
                union(a, union(b, c)) = union(union(a, b), c)
                [by modus_ponens step1 bwd-all]
            }
          @close-c |
            forall c: Set; union(a, union(b, c)) = union(union(a, b), c)
            [by forall_intro gen-c]
        }
      @close-b |
        forall b: Set; forall c: Set; union(a, union(b, c)) = union(union(a, b), c)
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; forall c: Set; union(a, union(b, c)) = union(union(a, b), c)
    [by forall_intro gen-a]
qed
```

```bpa
theorem intersectionAssociative: forall a, b, c: Set; intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @gen-c |
            fix c: Set {
              @ax-intersection |
                forall p, q: Set; forall x: Universe;
                  (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
                  and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
                [by axiom intersectionMember]
              @mem-intersection_b-c |
                forall x: Universe;
                  (member(x, intersection(b, c)) -> (member(x, b) and member(x, c)))
                  and ((member(x, b) and member(x, c)) -> member(x, intersection(b, c)))
                [by forall_elim(b, c) ax-intersection]
              @mem-intersection_a-intersection_b-c |
                forall x: Universe;
                  (member(x, intersection(a, intersection(b, c))) -> (member(x, a) and member(x, intersection(b, c))))
                  and ((member(x, a) and member(x, intersection(b, c))) -> member(x, intersection(a, intersection(b, c))))
                [by forall_elim(a, intersection(b, c)) ax-intersection]
              @mem-intersection_a-b |
                forall x: Universe;
                  (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
                  and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
                [by forall_elim(a, b) ax-intersection]
              @mem-intersection_intersection_a-b-c |
                forall x: Universe;
                  (member(x, intersection(intersection(a, b), c)) -> (member(x, intersection(a, b)) and member(x, c)))
                  and ((member(x, intersection(a, b)) and member(x, c)) -> member(x, intersection(intersection(a, b), c)))
                [by forall_elim(intersection(a, b), c) ax-intersection]
              @fwd |
                fix x: Universe {
                  @fwd-intersection_b-c |
                    (member(x, intersection(b, c)) -> (member(x, b) and member(x, c)))
                    and ((member(x, b) and member(x, c)) -> member(x, intersection(b, c)))
                    [by forall_elim(x) mem-intersection_b-c]
                  @fwd-intersection_a-intersection_b-c |
                    (member(x, intersection(a, intersection(b, c))) -> (member(x, a) and member(x, intersection(b, c))))
                    and ((member(x, a) and member(x, intersection(b, c))) -> member(x, intersection(a, intersection(b, c))))
                    [by forall_elim(x) mem-intersection_a-intersection_b-c]
                  @fwd-intersection_a-b |
                    (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
                    and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
                    [by forall_elim(x) mem-intersection_a-b]
                  @fwd-intersection_intersection_a-b-c |
                    (member(x, intersection(intersection(a, b), c)) -> (member(x, intersection(a, b)) and member(x, c)))
                    and ((member(x, intersection(a, b)) and member(x, c)) -> member(x, intersection(intersection(a, b), c)))
                    [by forall_elim(x) mem-intersection_intersection_a-b-c]
                  @fwd-assume |
                    assume member(x, intersection(a, intersection(b, c))) {
                      @fwd-hyp |
                        member(x, intersection(a, intersection(b, c)))
                        [by hypothesis fwd-assume]
                      @fwd-concl |
                        member(x, intersection(intersection(a, b), c))
                        [by tautology fwd-intersection_b-c fwd-intersection_a-intersection_b-c fwd-intersection_a-b fwd-intersection_intersection_a-b-c fwd-hyp]
                    }
                  @fwd-imp |
                    member(x, intersection(a, intersection(b, c))) -> member(x, intersection(intersection(a, b), c))
                    [by implies_intro fwd-assume]
                }
              @fwd-all |
                forall x: Universe; member(x, intersection(a, intersection(b, c))) -> member(x, intersection(intersection(a, b), c))
                [by forall_intro fwd]
              @bwd |
                fix y: Universe {
                  @bwd-intersection_b-c |
                    (member(y, intersection(b, c)) -> (member(y, b) and member(y, c)))
                    and ((member(y, b) and member(y, c)) -> member(y, intersection(b, c)))
                    [by forall_elim(y) mem-intersection_b-c]
                  @bwd-intersection_a-intersection_b-c |
                    (member(y, intersection(a, intersection(b, c))) -> (member(y, a) and member(y, intersection(b, c))))
                    and ((member(y, a) and member(y, intersection(b, c))) -> member(y, intersection(a, intersection(b, c))))
                    [by forall_elim(y) mem-intersection_a-intersection_b-c]
                  @bwd-intersection_a-b |
                    (member(y, intersection(a, b)) -> (member(y, a) and member(y, b)))
                    and ((member(y, a) and member(y, b)) -> member(y, intersection(a, b)))
                    [by forall_elim(y) mem-intersection_a-b]
                  @bwd-intersection_intersection_a-b-c |
                    (member(y, intersection(intersection(a, b), c)) -> (member(y, intersection(a, b)) and member(y, c)))
                    and ((member(y, intersection(a, b)) and member(y, c)) -> member(y, intersection(intersection(a, b), c)))
                    [by forall_elim(y) mem-intersection_intersection_a-b-c]
                  @bwd-assume |
                    assume member(y, intersection(intersection(a, b), c)) {
                      @bwd-hyp |
                        member(y, intersection(intersection(a, b), c))
                        [by hypothesis bwd-assume]
                      @bwd-concl |
                        member(y, intersection(a, intersection(b, c)))
                        [by tautology bwd-intersection_b-c bwd-intersection_a-intersection_b-c bwd-intersection_a-b bwd-intersection_intersection_a-b-c bwd-hyp]
                    }
                  @bwd-imp |
                    member(y, intersection(intersection(a, b), c)) -> member(y, intersection(a, intersection(b, c)))
                    [by implies_intro bwd-assume]
                }
              @bwd-all |
                forall y: Universe; member(y, intersection(intersection(a, b), c)) -> member(y, intersection(a, intersection(b, c)))
                [by forall_intro bwd]
              @ext |
                forall p, q: Set;
                  (forall x: Universe; member(x, p) -> member(x, q)) ->
                  (forall x: Universe; member(x, q) -> member(x, p)) ->
                  p = q
                [by axiom extensional]
              @ext-at |
                (forall x: Universe; member(x, intersection(a, intersection(b, c))) -> member(x, intersection(intersection(a, b), c))) ->
                (forall x: Universe; member(x, intersection(intersection(a, b), c)) -> member(x, intersection(a, intersection(b, c)))) ->
                intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
                [by forall_elim(intersection(a, intersection(b, c)), intersection(intersection(a, b), c)) ext]
              @step1 |
                (forall x: Universe; member(x, intersection(intersection(a, b), c)) -> member(x, intersection(a, intersection(b, c)))) ->
                intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
                [by modus_ponens ext-at fwd-all]
              @done |
                intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
                [by modus_ponens step1 bwd-all]
            }
          @close-c |
            forall c: Set; intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
            [by forall_intro gen-c]
        }
      @close-b |
        forall b: Set; forall c: Set; intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; forall c: Set; intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
    [by forall_intro gen-a]
qed
```

**(4)** Both operations are *commutative*.

```bpa
theorem unionCommutative: forall a, b: Set; union(a, b) = union(b, a)
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @ax-union |
            forall p, q: Set; forall x: Universe;
              (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
              and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
            [by axiom unionMember]
          @mem-union_a-b |
            forall x: Universe;
              (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
              and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
            [by forall_elim(a, b) ax-union]
          @mem-union_b-a |
            forall x: Universe;
              (member(x, union(b, a)) -> (member(x, b) or member(x, a)))
              and ((member(x, b) or member(x, a)) -> member(x, union(b, a)))
            [by forall_elim(b, a) ax-union]
          @fwd |
            fix x: Universe {
              @fwd-union_a-b |
                (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
                and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
                [by forall_elim(x) mem-union_a-b]
              @fwd-union_b-a |
                (member(x, union(b, a)) -> (member(x, b) or member(x, a)))
                and ((member(x, b) or member(x, a)) -> member(x, union(b, a)))
                [by forall_elim(x) mem-union_b-a]
              @fwd-assume |
                assume member(x, union(a, b)) {
                  @fwd-hyp |
                    member(x, union(a, b))
                    [by hypothesis fwd-assume]
                  @fwd-concl |
                    member(x, union(b, a))
                    [by tautology fwd-union_a-b fwd-union_b-a fwd-hyp]
                }
              @fwd-imp |
                member(x, union(a, b)) -> member(x, union(b, a))
                [by implies_intro fwd-assume]
            }
          @fwd-all |
            forall x: Universe; member(x, union(a, b)) -> member(x, union(b, a))
            [by forall_intro fwd]
          @bwd |
            fix y: Universe {
              @bwd-union_a-b |
                (member(y, union(a, b)) -> (member(y, a) or member(y, b)))
                and ((member(y, a) or member(y, b)) -> member(y, union(a, b)))
                [by forall_elim(y) mem-union_a-b]
              @bwd-union_b-a |
                (member(y, union(b, a)) -> (member(y, b) or member(y, a)))
                and ((member(y, b) or member(y, a)) -> member(y, union(b, a)))
                [by forall_elim(y) mem-union_b-a]
              @bwd-assume |
                assume member(y, union(b, a)) {
                  @bwd-hyp |
                    member(y, union(b, a))
                    [by hypothesis bwd-assume]
                  @bwd-concl |
                    member(y, union(a, b))
                    [by tautology bwd-union_a-b bwd-union_b-a bwd-hyp]
                }
              @bwd-imp |
                member(y, union(b, a)) -> member(y, union(a, b))
                [by implies_intro bwd-assume]
            }
          @bwd-all |
            forall y: Universe; member(y, union(b, a)) -> member(y, union(a, b))
            [by forall_intro bwd]
          @ext |
            forall p, q: Set;
              (forall x: Universe; member(x, p) -> member(x, q)) ->
              (forall x: Universe; member(x, q) -> member(x, p)) ->
              p = q
            [by axiom extensional]
          @ext-at |
            (forall x: Universe; member(x, union(a, b)) -> member(x, union(b, a))) ->
            (forall x: Universe; member(x, union(b, a)) -> member(x, union(a, b))) ->
            union(a, b) = union(b, a)
            [by forall_elim(union(a, b), union(b, a)) ext]
          @step1 |
            (forall x: Universe; member(x, union(b, a)) -> member(x, union(a, b))) ->
            union(a, b) = union(b, a)
            [by modus_ponens ext-at fwd-all]
          @done |
            union(a, b) = union(b, a)
            [by modus_ponens step1 bwd-all]
        }
      @close-b |
        forall b: Set; union(a, b) = union(b, a)
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; union(a, b) = union(b, a)
    [by forall_intro gen-a]
qed
```

```bpa
theorem intersectionCommutative: forall a, b: Set; intersection(a, b) = intersection(b, a)
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @ax-intersection |
            forall p, q: Set; forall x: Universe;
              (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
              and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
            [by axiom intersectionMember]
          @mem-intersection_a-b |
            forall x: Universe;
              (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
              and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
            [by forall_elim(a, b) ax-intersection]
          @mem-intersection_b-a |
            forall x: Universe;
              (member(x, intersection(b, a)) -> (member(x, b) and member(x, a)))
              and ((member(x, b) and member(x, a)) -> member(x, intersection(b, a)))
            [by forall_elim(b, a) ax-intersection]
          @fwd |
            fix x: Universe {
              @fwd-intersection_a-b |
                (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
                and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
                [by forall_elim(x) mem-intersection_a-b]
              @fwd-intersection_b-a |
                (member(x, intersection(b, a)) -> (member(x, b) and member(x, a)))
                and ((member(x, b) and member(x, a)) -> member(x, intersection(b, a)))
                [by forall_elim(x) mem-intersection_b-a]
              @fwd-assume |
                assume member(x, intersection(a, b)) {
                  @fwd-hyp |
                    member(x, intersection(a, b))
                    [by hypothesis fwd-assume]
                  @fwd-concl |
                    member(x, intersection(b, a))
                    [by tautology fwd-intersection_a-b fwd-intersection_b-a fwd-hyp]
                }
              @fwd-imp |
                member(x, intersection(a, b)) -> member(x, intersection(b, a))
                [by implies_intro fwd-assume]
            }
          @fwd-all |
            forall x: Universe; member(x, intersection(a, b)) -> member(x, intersection(b, a))
            [by forall_intro fwd]
          @bwd |
            fix y: Universe {
              @bwd-intersection_a-b |
                (member(y, intersection(a, b)) -> (member(y, a) and member(y, b)))
                and ((member(y, a) and member(y, b)) -> member(y, intersection(a, b)))
                [by forall_elim(y) mem-intersection_a-b]
              @bwd-intersection_b-a |
                (member(y, intersection(b, a)) -> (member(y, b) and member(y, a)))
                and ((member(y, b) and member(y, a)) -> member(y, intersection(b, a)))
                [by forall_elim(y) mem-intersection_b-a]
              @bwd-assume |
                assume member(y, intersection(b, a)) {
                  @bwd-hyp |
                    member(y, intersection(b, a))
                    [by hypothesis bwd-assume]
                  @bwd-concl |
                    member(y, intersection(a, b))
                    [by tautology bwd-intersection_a-b bwd-intersection_b-a bwd-hyp]
                }
              @bwd-imp |
                member(y, intersection(b, a)) -> member(y, intersection(a, b))
                [by implies_intro bwd-assume]
            }
          @bwd-all |
            forall y: Universe; member(y, intersection(b, a)) -> member(y, intersection(a, b))
            [by forall_intro bwd]
          @ext |
            forall p, q: Set;
              (forall x: Universe; member(x, p) -> member(x, q)) ->
              (forall x: Universe; member(x, q) -> member(x, p)) ->
              p = q
            [by axiom extensional]
          @ext-at |
            (forall x: Universe; member(x, intersection(a, b)) -> member(x, intersection(b, a))) ->
            (forall x: Universe; member(x, intersection(b, a)) -> member(x, intersection(a, b))) ->
            intersection(a, b) = intersection(b, a)
            [by forall_elim(intersection(a, b), intersection(b, a)) ext]
          @step1 |
            (forall x: Universe; member(x, intersection(b, a)) -> member(x, intersection(a, b))) ->
            intersection(a, b) = intersection(b, a)
            [by modus_ponens ext-at fwd-all]
          @done |
            intersection(a, b) = intersection(b, a)
            [by modus_ponens step1 bwd-all]
        }
      @close-b |
        forall b: Set; intersection(a, b) = intersection(b, a)
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; intersection(a, b) = intersection(b, a)
    [by forall_intro gen-a]
qed
```

**(5)–(6)** Each operation *distributes* over the other, mirroring the two
propositional distributive laws.

```bpa
theorem unionDistributesOverIntersection: forall a, b, c: Set; union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @gen-c |
            fix c: Set {
              @ax-intersection |
                forall p, q: Set; forall x: Universe;
                  (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
                  and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
                [by axiom intersectionMember]
              @ax-union |
                forall p, q: Set; forall x: Universe;
                  (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
                  and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
                [by axiom unionMember]
              @mem-intersection_b-c |
                forall x: Universe;
                  (member(x, intersection(b, c)) -> (member(x, b) and member(x, c)))
                  and ((member(x, b) and member(x, c)) -> member(x, intersection(b, c)))
                [by forall_elim(b, c) ax-intersection]
              @mem-union_a-intersection_b-c |
                forall x: Universe;
                  (member(x, union(a, intersection(b, c))) -> (member(x, a) or member(x, intersection(b, c))))
                  and ((member(x, a) or member(x, intersection(b, c))) -> member(x, union(a, intersection(b, c))))
                [by forall_elim(a, intersection(b, c)) ax-union]
              @mem-union_a-b |
                forall x: Universe;
                  (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
                  and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
                [by forall_elim(a, b) ax-union]
              @mem-union_a-c |
                forall x: Universe;
                  (member(x, union(a, c)) -> (member(x, a) or member(x, c)))
                  and ((member(x, a) or member(x, c)) -> member(x, union(a, c)))
                [by forall_elim(a, c) ax-union]
              @mem-intersection_union_a-b-union_a-c |
                forall x: Universe;
                  (member(x, intersection(union(a, b), union(a, c))) -> (member(x, union(a, b)) and member(x, union(a, c))))
                  and ((member(x, union(a, b)) and member(x, union(a, c))) -> member(x, intersection(union(a, b), union(a, c))))
                [by forall_elim(union(a, b), union(a, c)) ax-intersection]
              @fwd |
                fix x: Universe {
                  @fwd-intersection_b-c |
                    (member(x, intersection(b, c)) -> (member(x, b) and member(x, c)))
                    and ((member(x, b) and member(x, c)) -> member(x, intersection(b, c)))
                    [by forall_elim(x) mem-intersection_b-c]
                  @fwd-union_a-intersection_b-c |
                    (member(x, union(a, intersection(b, c))) -> (member(x, a) or member(x, intersection(b, c))))
                    and ((member(x, a) or member(x, intersection(b, c))) -> member(x, union(a, intersection(b, c))))
                    [by forall_elim(x) mem-union_a-intersection_b-c]
                  @fwd-union_a-b |
                    (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
                    and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
                    [by forall_elim(x) mem-union_a-b]
                  @fwd-union_a-c |
                    (member(x, union(a, c)) -> (member(x, a) or member(x, c)))
                    and ((member(x, a) or member(x, c)) -> member(x, union(a, c)))
                    [by forall_elim(x) mem-union_a-c]
                  @fwd-intersection_union_a-b-union_a-c |
                    (member(x, intersection(union(a, b), union(a, c))) -> (member(x, union(a, b)) and member(x, union(a, c))))
                    and ((member(x, union(a, b)) and member(x, union(a, c))) -> member(x, intersection(union(a, b), union(a, c))))
                    [by forall_elim(x) mem-intersection_union_a-b-union_a-c]
                  @fwd-assume |
                    assume member(x, union(a, intersection(b, c))) {
                      @fwd-hyp |
                        member(x, union(a, intersection(b, c)))
                        [by hypothesis fwd-assume]
                      @fwd-concl |
                        member(x, intersection(union(a, b), union(a, c)))
                        [by tautology fwd-intersection_b-c fwd-union_a-intersection_b-c fwd-union_a-b fwd-union_a-c fwd-intersection_union_a-b-union_a-c fwd-hyp]
                    }
                  @fwd-imp |
                    member(x, union(a, intersection(b, c))) -> member(x, intersection(union(a, b), union(a, c)))
                    [by implies_intro fwd-assume]
                }
              @fwd-all |
                forall x: Universe; member(x, union(a, intersection(b, c))) -> member(x, intersection(union(a, b), union(a, c)))
                [by forall_intro fwd]
              @bwd |
                fix y: Universe {
                  @bwd-intersection_b-c |
                    (member(y, intersection(b, c)) -> (member(y, b) and member(y, c)))
                    and ((member(y, b) and member(y, c)) -> member(y, intersection(b, c)))
                    [by forall_elim(y) mem-intersection_b-c]
                  @bwd-union_a-intersection_b-c |
                    (member(y, union(a, intersection(b, c))) -> (member(y, a) or member(y, intersection(b, c))))
                    and ((member(y, a) or member(y, intersection(b, c))) -> member(y, union(a, intersection(b, c))))
                    [by forall_elim(y) mem-union_a-intersection_b-c]
                  @bwd-union_a-b |
                    (member(y, union(a, b)) -> (member(y, a) or member(y, b)))
                    and ((member(y, a) or member(y, b)) -> member(y, union(a, b)))
                    [by forall_elim(y) mem-union_a-b]
                  @bwd-union_a-c |
                    (member(y, union(a, c)) -> (member(y, a) or member(y, c)))
                    and ((member(y, a) or member(y, c)) -> member(y, union(a, c)))
                    [by forall_elim(y) mem-union_a-c]
                  @bwd-intersection_union_a-b-union_a-c |
                    (member(y, intersection(union(a, b), union(a, c))) -> (member(y, union(a, b)) and member(y, union(a, c))))
                    and ((member(y, union(a, b)) and member(y, union(a, c))) -> member(y, intersection(union(a, b), union(a, c))))
                    [by forall_elim(y) mem-intersection_union_a-b-union_a-c]
                  @bwd-assume |
                    assume member(y, intersection(union(a, b), union(a, c))) {
                      @bwd-hyp |
                        member(y, intersection(union(a, b), union(a, c)))
                        [by hypothesis bwd-assume]
                      @bwd-concl |
                        member(y, union(a, intersection(b, c)))
                        [by tautology bwd-intersection_b-c bwd-union_a-intersection_b-c bwd-union_a-b bwd-union_a-c bwd-intersection_union_a-b-union_a-c bwd-hyp]
                    }
                  @bwd-imp |
                    member(y, intersection(union(a, b), union(a, c))) -> member(y, union(a, intersection(b, c)))
                    [by implies_intro bwd-assume]
                }
              @bwd-all |
                forall y: Universe; member(y, intersection(union(a, b), union(a, c))) -> member(y, union(a, intersection(b, c)))
                [by forall_intro bwd]
              @ext |
                forall p, q: Set;
                  (forall x: Universe; member(x, p) -> member(x, q)) ->
                  (forall x: Universe; member(x, q) -> member(x, p)) ->
                  p = q
                [by axiom extensional]
              @ext-at |
                (forall x: Universe; member(x, union(a, intersection(b, c))) -> member(x, intersection(union(a, b), union(a, c)))) ->
                (forall x: Universe; member(x, intersection(union(a, b), union(a, c))) -> member(x, union(a, intersection(b, c)))) ->
                union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))
                [by forall_elim(union(a, intersection(b, c)), intersection(union(a, b), union(a, c))) ext]
              @step1 |
                (forall x: Universe; member(x, intersection(union(a, b), union(a, c))) -> member(x, union(a, intersection(b, c)))) ->
                union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))
                [by modus_ponens ext-at fwd-all]
              @done |
                union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))
                [by modus_ponens step1 bwd-all]
            }
          @close-c |
            forall c: Set; union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))
            [by forall_intro gen-c]
        }
      @close-b |
        forall b: Set; forall c: Set; union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; forall c: Set; union(a, intersection(b, c)) = intersection(union(a, b), union(a, c))
    [by forall_intro gen-a]
qed
```

```bpa
theorem intersectionDistributesOverUnion: forall a, b, c: Set; intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @gen-c |
            fix c: Set {
              @ax-union |
                forall p, q: Set; forall x: Universe;
                  (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
                  and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
                [by axiom unionMember]
              @ax-intersection |
                forall p, q: Set; forall x: Universe;
                  (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
                  and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
                [by axiom intersectionMember]
              @mem-union_b-c |
                forall x: Universe;
                  (member(x, union(b, c)) -> (member(x, b) or member(x, c)))
                  and ((member(x, b) or member(x, c)) -> member(x, union(b, c)))
                [by forall_elim(b, c) ax-union]
              @mem-intersection_a-union_b-c |
                forall x: Universe;
                  (member(x, intersection(a, union(b, c))) -> (member(x, a) and member(x, union(b, c))))
                  and ((member(x, a) and member(x, union(b, c))) -> member(x, intersection(a, union(b, c))))
                [by forall_elim(a, union(b, c)) ax-intersection]
              @mem-intersection_a-b |
                forall x: Universe;
                  (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
                  and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
                [by forall_elim(a, b) ax-intersection]
              @mem-intersection_a-c |
                forall x: Universe;
                  (member(x, intersection(a, c)) -> (member(x, a) and member(x, c)))
                  and ((member(x, a) and member(x, c)) -> member(x, intersection(a, c)))
                [by forall_elim(a, c) ax-intersection]
              @mem-union_intersection_a-b-intersection_a-c |
                forall x: Universe;
                  (member(x, union(intersection(a, b), intersection(a, c))) -> (member(x, intersection(a, b)) or member(x, intersection(a, c))))
                  and ((member(x, intersection(a, b)) or member(x, intersection(a, c))) -> member(x, union(intersection(a, b), intersection(a, c))))
                [by forall_elim(intersection(a, b), intersection(a, c)) ax-union]
              @fwd |
                fix x: Universe {
                  @fwd-union_b-c |
                    (member(x, union(b, c)) -> (member(x, b) or member(x, c)))
                    and ((member(x, b) or member(x, c)) -> member(x, union(b, c)))
                    [by forall_elim(x) mem-union_b-c]
                  @fwd-intersection_a-union_b-c |
                    (member(x, intersection(a, union(b, c))) -> (member(x, a) and member(x, union(b, c))))
                    and ((member(x, a) and member(x, union(b, c))) -> member(x, intersection(a, union(b, c))))
                    [by forall_elim(x) mem-intersection_a-union_b-c]
                  @fwd-intersection_a-b |
                    (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
                    and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
                    [by forall_elim(x) mem-intersection_a-b]
                  @fwd-intersection_a-c |
                    (member(x, intersection(a, c)) -> (member(x, a) and member(x, c)))
                    and ((member(x, a) and member(x, c)) -> member(x, intersection(a, c)))
                    [by forall_elim(x) mem-intersection_a-c]
                  @fwd-union_intersection_a-b-intersection_a-c |
                    (member(x, union(intersection(a, b), intersection(a, c))) -> (member(x, intersection(a, b)) or member(x, intersection(a, c))))
                    and ((member(x, intersection(a, b)) or member(x, intersection(a, c))) -> member(x, union(intersection(a, b), intersection(a, c))))
                    [by forall_elim(x) mem-union_intersection_a-b-intersection_a-c]
                  @fwd-assume |
                    assume member(x, intersection(a, union(b, c))) {
                      @fwd-hyp |
                        member(x, intersection(a, union(b, c)))
                        [by hypothesis fwd-assume]
                      @fwd-concl |
                        member(x, union(intersection(a, b), intersection(a, c)))
                        [by tautology fwd-union_b-c fwd-intersection_a-union_b-c fwd-intersection_a-b fwd-intersection_a-c fwd-union_intersection_a-b-intersection_a-c fwd-hyp]
                    }
                  @fwd-imp |
                    member(x, intersection(a, union(b, c))) -> member(x, union(intersection(a, b), intersection(a, c)))
                    [by implies_intro fwd-assume]
                }
              @fwd-all |
                forall x: Universe; member(x, intersection(a, union(b, c))) -> member(x, union(intersection(a, b), intersection(a, c)))
                [by forall_intro fwd]
              @bwd |
                fix y: Universe {
                  @bwd-union_b-c |
                    (member(y, union(b, c)) -> (member(y, b) or member(y, c)))
                    and ((member(y, b) or member(y, c)) -> member(y, union(b, c)))
                    [by forall_elim(y) mem-union_b-c]
                  @bwd-intersection_a-union_b-c |
                    (member(y, intersection(a, union(b, c))) -> (member(y, a) and member(y, union(b, c))))
                    and ((member(y, a) and member(y, union(b, c))) -> member(y, intersection(a, union(b, c))))
                    [by forall_elim(y) mem-intersection_a-union_b-c]
                  @bwd-intersection_a-b |
                    (member(y, intersection(a, b)) -> (member(y, a) and member(y, b)))
                    and ((member(y, a) and member(y, b)) -> member(y, intersection(a, b)))
                    [by forall_elim(y) mem-intersection_a-b]
                  @bwd-intersection_a-c |
                    (member(y, intersection(a, c)) -> (member(y, a) and member(y, c)))
                    and ((member(y, a) and member(y, c)) -> member(y, intersection(a, c)))
                    [by forall_elim(y) mem-intersection_a-c]
                  @bwd-union_intersection_a-b-intersection_a-c |
                    (member(y, union(intersection(a, b), intersection(a, c))) -> (member(y, intersection(a, b)) or member(y, intersection(a, c))))
                    and ((member(y, intersection(a, b)) or member(y, intersection(a, c))) -> member(y, union(intersection(a, b), intersection(a, c))))
                    [by forall_elim(y) mem-union_intersection_a-b-intersection_a-c]
                  @bwd-assume |
                    assume member(y, union(intersection(a, b), intersection(a, c))) {
                      @bwd-hyp |
                        member(y, union(intersection(a, b), intersection(a, c)))
                        [by hypothesis bwd-assume]
                      @bwd-concl |
                        member(y, intersection(a, union(b, c)))
                        [by tautology bwd-union_b-c bwd-intersection_a-union_b-c bwd-intersection_a-b bwd-intersection_a-c bwd-union_intersection_a-b-intersection_a-c bwd-hyp]
                    }
                  @bwd-imp |
                    member(y, union(intersection(a, b), intersection(a, c))) -> member(y, intersection(a, union(b, c)))
                    [by implies_intro bwd-assume]
                }
              @bwd-all |
                forall y: Universe; member(y, union(intersection(a, b), intersection(a, c))) -> member(y, intersection(a, union(b, c)))
                [by forall_intro bwd]
              @ext |
                forall p, q: Set;
                  (forall x: Universe; member(x, p) -> member(x, q)) ->
                  (forall x: Universe; member(x, q) -> member(x, p)) ->
                  p = q
                [by axiom extensional]
              @ext-at |
                (forall x: Universe; member(x, intersection(a, union(b, c))) -> member(x, union(intersection(a, b), intersection(a, c)))) ->
                (forall x: Universe; member(x, union(intersection(a, b), intersection(a, c))) -> member(x, intersection(a, union(b, c)))) ->
                intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))
                [by forall_elim(intersection(a, union(b, c)), union(intersection(a, b), intersection(a, c))) ext]
              @step1 |
                (forall x: Universe; member(x, union(intersection(a, b), intersection(a, c))) -> member(x, intersection(a, union(b, c)))) ->
                intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))
                [by modus_ponens ext-at fwd-all]
              @done |
                intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))
                [by modus_ponens step1 bwd-all]
            }
          @close-c |
            forall c: Set; intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))
            [by forall_intro gen-c]
        }
      @close-b |
        forall b: Set; forall c: Set; intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; forall c: Set; intersection(a, union(b, c)) = union(intersection(a, b), intersection(a, c))
    [by forall_intro gen-a]
qed
```

## Theorem — De Morgan's Laws

> Let $A$ and $B$ be sets. Then
>
> 1. $(A \cup B)' = A' \cap B'$;
> 2. $(A \cap B)' = A' \cup B'$.

The book's proof of (1) fixes an element $x \in (A \cup B)'$, observes
$x \notin A \cup B$ so $x$ is in neither $A$ nor $B$, hence $x \in A'$ and
$x \in B'$, i.e. $x \in A' \cap B'$ — and then runs the reverse inclusion. Our
`bpa` proof is that same two-inclusion argument, with the neither-nor step
handled by `complementMember` + `unionMember` feeding one `tautology`. The book
leaves (2) as an exercise; we prove it too.

```bpa
theorem deMorganUnion: forall a, b: Set; complement(union(a, b)) = intersection(complement(a), complement(b))
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @ax-union |
            forall p, q: Set; forall x: Universe;
              (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
              and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
            [by axiom unionMember]
          @ax-complement |
            forall p: Set; forall x: Universe;
              (member(x, complement(p)) -> (not member(x, p)))
              and ((not member(x, p)) -> member(x, complement(p)))
            [by axiom complementMember]
          @ax-intersection |
            forall p, q: Set; forall x: Universe;
              (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
              and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
            [by axiom intersectionMember]
          @mem-union_a-b |
            forall x: Universe;
              (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
              and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
            [by forall_elim(a, b) ax-union]
          @mem-complement_union_a-b |
            forall x: Universe;
              (member(x, complement(union(a, b))) -> (not member(x, union(a, b))))
              and ((not member(x, union(a, b))) -> member(x, complement(union(a, b))))
            [by forall_elim(union(a, b)) ax-complement]
          @mem-complement_a |
            forall x: Universe;
              (member(x, complement(a)) -> (not member(x, a)))
              and ((not member(x, a)) -> member(x, complement(a)))
            [by forall_elim(a) ax-complement]
          @mem-complement_b |
            forall x: Universe;
              (member(x, complement(b)) -> (not member(x, b)))
              and ((not member(x, b)) -> member(x, complement(b)))
            [by forall_elim(b) ax-complement]
          @mem-intersection_complement_a-complement_b |
            forall x: Universe;
              (member(x, intersection(complement(a), complement(b))) -> (member(x, complement(a)) and member(x, complement(b))))
              and ((member(x, complement(a)) and member(x, complement(b))) -> member(x, intersection(complement(a), complement(b))))
            [by forall_elim(complement(a), complement(b)) ax-intersection]
          @fwd |
            fix x: Universe {
              @fwd-union_a-b |
                (member(x, union(a, b)) -> (member(x, a) or member(x, b)))
                and ((member(x, a) or member(x, b)) -> member(x, union(a, b)))
                [by forall_elim(x) mem-union_a-b]
              @fwd-complement_union_a-b |
                (member(x, complement(union(a, b))) -> (not member(x, union(a, b))))
                and ((not member(x, union(a, b))) -> member(x, complement(union(a, b))))
                [by forall_elim(x) mem-complement_union_a-b]
              @fwd-complement_a |
                (member(x, complement(a)) -> (not member(x, a)))
                and ((not member(x, a)) -> member(x, complement(a)))
                [by forall_elim(x) mem-complement_a]
              @fwd-complement_b |
                (member(x, complement(b)) -> (not member(x, b)))
                and ((not member(x, b)) -> member(x, complement(b)))
                [by forall_elim(x) mem-complement_b]
              @fwd-intersection_complement_a-complement_b |
                (member(x, intersection(complement(a), complement(b))) -> (member(x, complement(a)) and member(x, complement(b))))
                and ((member(x, complement(a)) and member(x, complement(b))) -> member(x, intersection(complement(a), complement(b))))
                [by forall_elim(x) mem-intersection_complement_a-complement_b]
              @fwd-assume |
                assume member(x, complement(union(a, b))) {
                  @fwd-hyp |
                    member(x, complement(union(a, b)))
                    [by hypothesis fwd-assume]
                  @fwd-concl |
                    member(x, intersection(complement(a), complement(b)))
                    [by tautology fwd-union_a-b fwd-complement_union_a-b fwd-complement_a fwd-complement_b fwd-intersection_complement_a-complement_b fwd-hyp]
                }
              @fwd-imp |
                member(x, complement(union(a, b))) -> member(x, intersection(complement(a), complement(b)))
                [by implies_intro fwd-assume]
            }
          @fwd-all |
            forall x: Universe; member(x, complement(union(a, b))) -> member(x, intersection(complement(a), complement(b)))
            [by forall_intro fwd]
          @bwd |
            fix y: Universe {
              @bwd-union_a-b |
                (member(y, union(a, b)) -> (member(y, a) or member(y, b)))
                and ((member(y, a) or member(y, b)) -> member(y, union(a, b)))
                [by forall_elim(y) mem-union_a-b]
              @bwd-complement_union_a-b |
                (member(y, complement(union(a, b))) -> (not member(y, union(a, b))))
                and ((not member(y, union(a, b))) -> member(y, complement(union(a, b))))
                [by forall_elim(y) mem-complement_union_a-b]
              @bwd-complement_a |
                (member(y, complement(a)) -> (not member(y, a)))
                and ((not member(y, a)) -> member(y, complement(a)))
                [by forall_elim(y) mem-complement_a]
              @bwd-complement_b |
                (member(y, complement(b)) -> (not member(y, b)))
                and ((not member(y, b)) -> member(y, complement(b)))
                [by forall_elim(y) mem-complement_b]
              @bwd-intersection_complement_a-complement_b |
                (member(y, intersection(complement(a), complement(b))) -> (member(y, complement(a)) and member(y, complement(b))))
                and ((member(y, complement(a)) and member(y, complement(b))) -> member(y, intersection(complement(a), complement(b))))
                [by forall_elim(y) mem-intersection_complement_a-complement_b]
              @bwd-assume |
                assume member(y, intersection(complement(a), complement(b))) {
                  @bwd-hyp |
                    member(y, intersection(complement(a), complement(b)))
                    [by hypothesis bwd-assume]
                  @bwd-concl |
                    member(y, complement(union(a, b)))
                    [by tautology bwd-union_a-b bwd-complement_union_a-b bwd-complement_a bwd-complement_b bwd-intersection_complement_a-complement_b bwd-hyp]
                }
              @bwd-imp |
                member(y, intersection(complement(a), complement(b))) -> member(y, complement(union(a, b)))
                [by implies_intro bwd-assume]
            }
          @bwd-all |
            forall y: Universe; member(y, intersection(complement(a), complement(b))) -> member(y, complement(union(a, b)))
            [by forall_intro bwd]
          @ext |
            forall p, q: Set;
              (forall x: Universe; member(x, p) -> member(x, q)) ->
              (forall x: Universe; member(x, q) -> member(x, p)) ->
              p = q
            [by axiom extensional]
          @ext-at |
            (forall x: Universe; member(x, complement(union(a, b))) -> member(x, intersection(complement(a), complement(b)))) ->
            (forall x: Universe; member(x, intersection(complement(a), complement(b))) -> member(x, complement(union(a, b)))) ->
            complement(union(a, b)) = intersection(complement(a), complement(b))
            [by forall_elim(complement(union(a, b)), intersection(complement(a), complement(b))) ext]
          @step1 |
            (forall x: Universe; member(x, intersection(complement(a), complement(b))) -> member(x, complement(union(a, b)))) ->
            complement(union(a, b)) = intersection(complement(a), complement(b))
            [by modus_ponens ext-at fwd-all]
          @done |
            complement(union(a, b)) = intersection(complement(a), complement(b))
            [by modus_ponens step1 bwd-all]
        }
      @close-b |
        forall b: Set; complement(union(a, b)) = intersection(complement(a), complement(b))
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; complement(union(a, b)) = intersection(complement(a), complement(b))
    [by forall_intro gen-a]
qed
```

```bpa
theorem deMorganIntersection: forall a, b: Set; complement(intersection(a, b)) = union(complement(a), complement(b))
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @ax-intersection |
            forall p, q: Set; forall x: Universe;
              (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
              and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
            [by axiom intersectionMember]
          @ax-complement |
            forall p: Set; forall x: Universe;
              (member(x, complement(p)) -> (not member(x, p)))
              and ((not member(x, p)) -> member(x, complement(p)))
            [by axiom complementMember]
          @ax-union |
            forall p, q: Set; forall x: Universe;
              (member(x, union(p, q)) -> (member(x, p) or member(x, q)))
              and ((member(x, p) or member(x, q)) -> member(x, union(p, q)))
            [by axiom unionMember]
          @mem-intersection_a-b |
            forall x: Universe;
              (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
              and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
            [by forall_elim(a, b) ax-intersection]
          @mem-complement_intersection_a-b |
            forall x: Universe;
              (member(x, complement(intersection(a, b))) -> (not member(x, intersection(a, b))))
              and ((not member(x, intersection(a, b))) -> member(x, complement(intersection(a, b))))
            [by forall_elim(intersection(a, b)) ax-complement]
          @mem-complement_a |
            forall x: Universe;
              (member(x, complement(a)) -> (not member(x, a)))
              and ((not member(x, a)) -> member(x, complement(a)))
            [by forall_elim(a) ax-complement]
          @mem-complement_b |
            forall x: Universe;
              (member(x, complement(b)) -> (not member(x, b)))
              and ((not member(x, b)) -> member(x, complement(b)))
            [by forall_elim(b) ax-complement]
          @mem-union_complement_a-complement_b |
            forall x: Universe;
              (member(x, union(complement(a), complement(b))) -> (member(x, complement(a)) or member(x, complement(b))))
              and ((member(x, complement(a)) or member(x, complement(b))) -> member(x, union(complement(a), complement(b))))
            [by forall_elim(complement(a), complement(b)) ax-union]
          @fwd |
            fix x: Universe {
              @fwd-intersection_a-b |
                (member(x, intersection(a, b)) -> (member(x, a) and member(x, b)))
                and ((member(x, a) and member(x, b)) -> member(x, intersection(a, b)))
                [by forall_elim(x) mem-intersection_a-b]
              @fwd-complement_intersection_a-b |
                (member(x, complement(intersection(a, b))) -> (not member(x, intersection(a, b))))
                and ((not member(x, intersection(a, b))) -> member(x, complement(intersection(a, b))))
                [by forall_elim(x) mem-complement_intersection_a-b]
              @fwd-complement_a |
                (member(x, complement(a)) -> (not member(x, a)))
                and ((not member(x, a)) -> member(x, complement(a)))
                [by forall_elim(x) mem-complement_a]
              @fwd-complement_b |
                (member(x, complement(b)) -> (not member(x, b)))
                and ((not member(x, b)) -> member(x, complement(b)))
                [by forall_elim(x) mem-complement_b]
              @fwd-union_complement_a-complement_b |
                (member(x, union(complement(a), complement(b))) -> (member(x, complement(a)) or member(x, complement(b))))
                and ((member(x, complement(a)) or member(x, complement(b))) -> member(x, union(complement(a), complement(b))))
                [by forall_elim(x) mem-union_complement_a-complement_b]
              @fwd-assume |
                assume member(x, complement(intersection(a, b))) {
                  @fwd-hyp |
                    member(x, complement(intersection(a, b)))
                    [by hypothesis fwd-assume]
                  @fwd-concl |
                    member(x, union(complement(a), complement(b)))
                    [by tautology fwd-intersection_a-b fwd-complement_intersection_a-b fwd-complement_a fwd-complement_b fwd-union_complement_a-complement_b fwd-hyp]
                }
              @fwd-imp |
                member(x, complement(intersection(a, b))) -> member(x, union(complement(a), complement(b)))
                [by implies_intro fwd-assume]
            }
          @fwd-all |
            forall x: Universe; member(x, complement(intersection(a, b))) -> member(x, union(complement(a), complement(b)))
            [by forall_intro fwd]
          @bwd |
            fix y: Universe {
              @bwd-intersection_a-b |
                (member(y, intersection(a, b)) -> (member(y, a) and member(y, b)))
                and ((member(y, a) and member(y, b)) -> member(y, intersection(a, b)))
                [by forall_elim(y) mem-intersection_a-b]
              @bwd-complement_intersection_a-b |
                (member(y, complement(intersection(a, b))) -> (not member(y, intersection(a, b))))
                and ((not member(y, intersection(a, b))) -> member(y, complement(intersection(a, b))))
                [by forall_elim(y) mem-complement_intersection_a-b]
              @bwd-complement_a |
                (member(y, complement(a)) -> (not member(y, a)))
                and ((not member(y, a)) -> member(y, complement(a)))
                [by forall_elim(y) mem-complement_a]
              @bwd-complement_b |
                (member(y, complement(b)) -> (not member(y, b)))
                and ((not member(y, b)) -> member(y, complement(b)))
                [by forall_elim(y) mem-complement_b]
              @bwd-union_complement_a-complement_b |
                (member(y, union(complement(a), complement(b))) -> (member(y, complement(a)) or member(y, complement(b))))
                and ((member(y, complement(a)) or member(y, complement(b))) -> member(y, union(complement(a), complement(b))))
                [by forall_elim(y) mem-union_complement_a-complement_b]
              @bwd-assume |
                assume member(y, union(complement(a), complement(b))) {
                  @bwd-hyp |
                    member(y, union(complement(a), complement(b)))
                    [by hypothesis bwd-assume]
                  @bwd-concl |
                    member(y, complement(intersection(a, b)))
                    [by tautology bwd-intersection_a-b bwd-complement_intersection_a-b bwd-complement_a bwd-complement_b bwd-union_complement_a-complement_b bwd-hyp]
                }
              @bwd-imp |
                member(y, union(complement(a), complement(b))) -> member(y, complement(intersection(a, b)))
                [by implies_intro bwd-assume]
            }
          @bwd-all |
            forall y: Universe; member(y, union(complement(a), complement(b))) -> member(y, complement(intersection(a, b)))
            [by forall_intro bwd]
          @ext |
            forall p, q: Set;
              (forall x: Universe; member(x, p) -> member(x, q)) ->
              (forall x: Universe; member(x, q) -> member(x, p)) ->
              p = q
            [by axiom extensional]
          @ext-at |
            (forall x: Universe; member(x, complement(intersection(a, b))) -> member(x, union(complement(a), complement(b)))) ->
            (forall x: Universe; member(x, union(complement(a), complement(b))) -> member(x, complement(intersection(a, b)))) ->
            complement(intersection(a, b)) = union(complement(a), complement(b))
            [by forall_elim(complement(intersection(a, b)), union(complement(a), complement(b))) ext]
          @step1 |
            (forall x: Universe; member(x, union(complement(a), complement(b))) -> member(x, complement(intersection(a, b)))) ->
            complement(intersection(a, b)) = union(complement(a), complement(b))
            [by modus_ponens ext-at fwd-all]
          @done |
            complement(intersection(a, b)) = union(complement(a), complement(b))
            [by modus_ponens step1 bwd-all]
        }
      @close-b |
        forall b: Set; complement(intersection(a, b)) = union(complement(a), complement(b))
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; complement(intersection(a, b)) = union(complement(a), complement(b))
    [by forall_intro gen-a]
qed
```

**Example.** Other relations between sets often hold true. For example,

$$(A \setminus B) \cap (B \setminus A) = \emptyset.$$

To see that this is true, observe that

$$(A \setminus B) \cap (B \setminus A) = (A \cap B') \cap (B \cap A') = A \cap A' \cap B \cap B' = \emptyset.$$

This identity *is* expressible in `std/set.bpa` and provable by the same
extensionality + `tautology` recipe (unfold both differences and both
complements at a fixed `x`; the conjunction contains `member(x,a)` alongside
`not member(x,a)`, a contradiction). We record it here as a worked instance of
the recipe:

```bpa
theorem disjointDifferences: forall a, b: Set; intersection(difference(a, b), difference(b, a)) = emptyset
proof
  @gen-a |
    fix a: Set {
      @gen-b |
        fix b: Set {
          @ax-difference |
            forall p, q: Set; forall x: Universe;
              (member(x, difference(p, q)) -> (member(x, p) and (not member(x, q))))
              and ((member(x, p) and (not member(x, q))) -> member(x, difference(p, q)))
            [by axiom differenceMember]
          @ax-intersection |
            forall p, q: Set; forall x: Universe;
              (member(x, intersection(p, q)) -> (member(x, p) and member(x, q)))
              and ((member(x, p) and member(x, q)) -> member(x, intersection(p, q)))
            [by axiom intersectionMember]
          @mem-difference_a-b |
            forall x: Universe;
              (member(x, difference(a, b)) -> (member(x, a) and (not member(x, b))))
              and ((member(x, a) and (not member(x, b))) -> member(x, difference(a, b)))
            [by forall_elim(a, b) ax-difference]
          @mem-difference_b-a |
            forall x: Universe;
              (member(x, difference(b, a)) -> (member(x, b) and (not member(x, a))))
              and ((member(x, b) and (not member(x, a))) -> member(x, difference(b, a)))
            [by forall_elim(b, a) ax-difference]
          @mem-intersection_difference_a-b-difference_b-a |
            forall x: Universe;
              (member(x, intersection(difference(a, b), difference(b, a))) -> (member(x, difference(a, b)) and member(x, difference(b, a))))
              and ((member(x, difference(a, b)) and member(x, difference(b, a))) -> member(x, intersection(difference(a, b), difference(b, a))))
            [by forall_elim(difference(a, b), difference(b, a)) ax-intersection]
          @ax-empty |
            forall x: Universe; not member(x, emptyset)
            [by axiom emptysetMember]
          @fwd |
            fix x: Universe {
              @fwd-difference_a-b |
                (member(x, difference(a, b)) -> (member(x, a) and (not member(x, b))))
                and ((member(x, a) and (not member(x, b))) -> member(x, difference(a, b)))
                [by forall_elim(x) mem-difference_a-b]
              @fwd-difference_b-a |
                (member(x, difference(b, a)) -> (member(x, b) and (not member(x, a))))
                and ((member(x, b) and (not member(x, a))) -> member(x, difference(b, a)))
                [by forall_elim(x) mem-difference_b-a]
              @fwd-intersection_difference_a-b-difference_b-a |
                (member(x, intersection(difference(a, b), difference(b, a))) -> (member(x, difference(a, b)) and member(x, difference(b, a))))
                and ((member(x, difference(a, b)) and member(x, difference(b, a))) -> member(x, intersection(difference(a, b), difference(b, a))))
                [by forall_elim(x) mem-intersection_difference_a-b-difference_b-a]
              @fwd-empty |
                not member(x, emptyset)
                [by forall_elim(x) ax-empty]
              @fwd-assume |
                assume member(x, intersection(difference(a, b), difference(b, a))) {
                  @fwd-hyp |
                    member(x, intersection(difference(a, b), difference(b, a)))
                    [by hypothesis fwd-assume]
                  @fwd-concl |
                    member(x, emptyset)
                    [by tautology fwd-difference_a-b fwd-difference_b-a fwd-intersection_difference_a-b-difference_b-a fwd-empty fwd-hyp]
                }
              @fwd-imp |
                member(x, intersection(difference(a, b), difference(b, a))) -> member(x, emptyset)
                [by implies_intro fwd-assume]
            }
          @fwd-all |
            forall x: Universe; member(x, intersection(difference(a, b), difference(b, a))) -> member(x, emptyset)
            [by forall_intro fwd]
          @bwd |
            fix y: Universe {
              @bwd-difference_a-b |
                (member(y, difference(a, b)) -> (member(y, a) and (not member(y, b))))
                and ((member(y, a) and (not member(y, b))) -> member(y, difference(a, b)))
                [by forall_elim(y) mem-difference_a-b]
              @bwd-difference_b-a |
                (member(y, difference(b, a)) -> (member(y, b) and (not member(y, a))))
                and ((member(y, b) and (not member(y, a))) -> member(y, difference(b, a)))
                [by forall_elim(y) mem-difference_b-a]
              @bwd-intersection_difference_a-b-difference_b-a |
                (member(y, intersection(difference(a, b), difference(b, a))) -> (member(y, difference(a, b)) and member(y, difference(b, a))))
                and ((member(y, difference(a, b)) and member(y, difference(b, a))) -> member(y, intersection(difference(a, b), difference(b, a))))
                [by forall_elim(y) mem-intersection_difference_a-b-difference_b-a]
              @bwd-empty |
                not member(y, emptyset)
                [by forall_elim(y) ax-empty]
              @bwd-assume |
                assume member(y, emptyset) {
                  @bwd-hyp |
                    member(y, emptyset)
                    [by hypothesis bwd-assume]
                  @bwd-concl |
                    member(y, intersection(difference(a, b), difference(b, a)))
                    [by tautology bwd-difference_a-b bwd-difference_b-a bwd-intersection_difference_a-b-difference_b-a bwd-empty bwd-hyp]
                }
              @bwd-imp |
                member(y, emptyset) -> member(y, intersection(difference(a, b), difference(b, a)))
                [by implies_intro bwd-assume]
            }
          @bwd-all |
            forall y: Universe; member(y, emptyset) -> member(y, intersection(difference(a, b), difference(b, a)))
            [by forall_intro bwd]
          @ext |
            forall p, q: Set;
              (forall x: Universe; member(x, p) -> member(x, q)) ->
              (forall x: Universe; member(x, q) -> member(x, p)) ->
              p = q
            [by axiom extensional]
          @ext-at |
            (forall x: Universe; member(x, intersection(difference(a, b), difference(b, a))) -> member(x, emptyset)) ->
            (forall x: Universe; member(x, emptyset) -> member(x, intersection(difference(a, b), difference(b, a)))) ->
            intersection(difference(a, b), difference(b, a)) = emptyset
            [by forall_elim(intersection(difference(a, b), difference(b, a)), emptyset) ext]
          @step1 |
            (forall x: Universe; member(x, emptyset) -> member(x, intersection(difference(a, b), difference(b, a)))) ->
            intersection(difference(a, b), difference(b, a)) = emptyset
            [by modus_ponens ext-at fwd-all]
          @done |
            intersection(difference(a, b), difference(b, a)) = emptyset
            [by modus_ponens step1 bwd-all]
        }
      @close-b |
        forall b: Set; intersection(difference(a, b), difference(b, a)) = emptyset
        [by forall_intro gen-b]
    }
  @close-a |
    forall a: Set; forall b: Set; intersection(difference(a, b), difference(b, a)) = emptyset
    [by forall_intro gen-a]
qed
```

---

## Deferred to later sections / files

- **§1.2.2 Cartesian Products and Mappings** — functions, composition, and the
  injective/surjective/bijective theory — is translated in
  [`aata/functions.md`](functions.md).
- **§1.2.3 Equivalence Relations and Partitions** is deferred: it needs a
  relation sort and sets-of-sets / quotient structure (equivalence classes
  $[a]$, the partition $X = \bigcup [x]$) that `std/set.bpa` does not model. See
  `aata/README`.
