# A literate proof with a bug

The `bpa` block below has a wrong step. `bpa check` must report the error at
the line number **in this `.md` file** (proving prose-masking preserves line
numbers), not at some extracted position.

Prose here pads the line count, so the error line is unambiguous.

```bpa
sort T
const A: T
const B: T

theorem wrong: A = B
proof
  @conclusion |
    A = B
    [by reflexivity]
qed
```

`reflexivity` proves `A = A`, not `A = B`, so the `@conclusion` claim is a
located error on line 16 (the `A = B` line) of THIS document.
