- bpa debug accelerant <line #? theorem-step?> to output the theorem produced by an accelerant
- finish rest of algebra book
- to-lean/isabelle/rocq mechanical export

positive-conclusion linear order — `by arithmetic` decides VALID but no certifier
  emits it: equation + strict bound ⊢ positive strict order, e.g.
  `add(x, b) = a -> less_than(ZERO, b) -> less_than(x, a)` (the in-fragment tail of
  peano-subtraction's subStrictlyDecreases, today hand-proved). Fix: an
  equation→order certifier that rearranges into lessThanIntro gap form. Distinct
  from the (landed) Cooper tail.


long-range:
persisent caching
build.zig.zon equivalent
make it faster (perf plan)
how to do numbers?