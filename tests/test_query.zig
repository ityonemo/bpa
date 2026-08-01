//! Integration gates — the `bpa query` subcommands (outline, theorem, whereis, search, uses, oracles).
//!
//! Each gate spawns the built `bpa` binary and asserts its stdout / stderr /
//! exit code; wired into the `test` step via `test_step.dependOn`.

const std = @import("std");
const Ctx = @import("Ctx.zig");

pub fn addTests(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    test_step: *std.Build.Step,
) void {
    const ctx = Ctx.init(b, exe, test_step);
    // `query outline <file> <theorem>`: the proof skeleton — bare labels,
    // with a header on each block opener (fix / assume / unpack / case).
    ctx.ok(&.{ "query", "outline", "tests/cases/outline.bpa", "everyoneIsQ" },
        \\theorem everyoneIsQ
        \\  generalize-n  fix n
        \\    cases
        \\    p-or-q
        \\    conclusion-inner  case on p-or-q
        \\      from-p  assume p(n)
        \\        p-holds
        \\        p-gives-q
        \\        p-gives-q-at-n
        \\        q-from-p
        \\      from-q  assume q(n)
        \\        q-holds
        \\  conclusion
        \\
    );

    // no theorem argument: outline every proof in the file (here, the one)
    ctx.ok(&.{ "query", "outline", "tests/cases/outline.bpa" },
        \\theorem everyoneIsQ
        \\  generalize-n  fix n
        \\    cases
        \\    p-or-q
        \\    conclusion-inner  case on p-or-q
        \\      from-p  assume p(n)
        \\        p-holds
        \\        p-gives-q
        \\        p-gives-q-at-n
        \\        q-from-p
        \\      from-q  assume q(n)
        \\        q-holds
        \\  conclusion
        \\
    );

    // a missing theorem is a located error on stderr (exit 1)
    ctx.fail(&.{ "query", "outline", "tests/cases/outline.bpa", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `query uses <file>`: per-proof rule tally + external citations. The
    // refs that are the proof's OWN labels are excluded from `cites`; the
    // axioms/theorems it pulls in are listed.
    ctx.ok(&.{ "query", "uses", "tests/cases/outline.bpa" },
        \\theorem everyoneIsQ
        \\  rules: axiom×2 forall_elim×2 hypothesis×2 modus_ponens forall_intro
        \\  cites: either pImpliesQ
        \\
    );

    // `query oracles <file>`: a proof with no oracle-capable rule reports
    // pure.
    ctx.ok(&.{ "query", "oracles", "tests/cases/outline.bpa" }, "no oracle-capable steps — this file's proofs are pure\n");

    // `query oracles <file>`: oracle-capable steps flagged at file:line:col
    // with the rule name — here both `assoc_quantified` and `assoc` (the
    // quantified variant runs the same oracle-capable core).
    ctx.ok(&.{ "query", "oracles", "tests/cases/assoc.bpa" },
        \\theorem reassoc1
        \\  tests/cases/assoc.bpa:19:9: assoc_quantified
        \\
        \\theorem reassoc2
        \\  tests/cases/assoc.bpa:28:9: assoc_quantified
        \\
        \\theorem reassoc3
        \\  tests/cases/assoc.bpa:45:25: assoc
        \\
    );

    // `query theorem <file> <name>`: the full source of the declaration,
    // verbatim — leading doc-comment through `qed`. Pinned to real std
    // (brittle by design: a std edit to this theorem should break here).
    const std_theorem_text =
        \\// Strategy: induction on n with prop(k) := add(k, ZERO) = k.
        \\// (addZeroLeft reduces ZERO on the LEFT; this is the mirror-image fact.)
        \\theorem addZeroRight: forall n: Nat; add(n, ZERO) = n
        \\proof
        \\  // base case: addZeroLeft specialized at b := ZERO
        \\  @add-zero-left |
        \\    forall b: Nat; add(ZERO, b) = b
        \\    [by axiom addZeroLeft]
        \\  @base-case |
        \\    add(ZERO, ZERO) = ZERO
        \\    [by forall_elim(ZERO) add-zero-left]
        \\
        \\  // inductive step: unfold add on succ(k), then rewrite with the IH
        \\  @induction-step |
        \\    fix k: Nat {
        \\      @given-inductive-hypothesis |
        \\        assume add(k, ZERO) = k {
        \\          @add-succ-left |
        \\            forall a, b: Nat; add(succ(a), b) = succ(add(a, b))
        \\            [by axiom addSuccLeft]
        \\          @unfolded |
        \\            add(succ(k), ZERO) = succ(add(k, ZERO))
        \\            [by forall_elim(k, ZERO) add-succ-left]
        \\          @inductive-hypothesis |
        \\            add(k, ZERO) = k
        \\            [by hypothesis given-inductive-hypothesis]
        \\          @succ-case |
        \\            add(succ(k), ZERO) = succ(k)
        \\            [by rewrite inductive-hypothesis unfolded]
        \\        }
        \\      @induction-step-at-k |
        \\        add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
        \\        [by implies_intro given-inductive-hypothesis]
        \\    }
        \\  @induction-step-for-all-k |
        \\    forall k: Nat; add(k, ZERO) = k -> add(succ(k), ZERO) = succ(k)
        \\    [by forall_intro induction-step]
        \\
        \\  @conclusion |
        \\    forall n: Nat; add(n, ZERO) = n
        \\    [by instantiate induction((fun k: Nat => add(k, ZERO) = k)) base-case induction-step-for-all-k]
        \\qed
        \\
    ;

    ctx.ok(&.{ "query", "theorem", "std/peano.bpa", "addZeroRight" }, std_theorem_text);

    // an ALIAS (`theorem addZeroRight = peano.addZeroRight` in subtraction)
    // resolves across files to the real proof — identical output.
    ctx.ok(&.{ "query", "theorem", "std/peano-subtraction.bpa", "addZeroRight" }, std_theorem_text);

    // a missing theorem: located error, exit 1
    ctx.fail(&.{ "query", "theorem", "std/peano.bpa", "noSuchThing" }, "error: no theorem 'noSuchThing' in this file\n");

    // `--sig`: just the statement, wrap-collapsed to one line, alias-
    // followed. `induction` wraps across two lines in the source.
    ctx.ok(&.{ "query", "theorem", "std/peano.bpa", "induction", "--sig" }, "axiom induction(prop: Nat -> Prop): prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)\n");

    // `query whereis <file> <ident>`: trace an alias across files to its
    // origin. Pinned to real std (brittle by design). `sub` is a func
    // aliased in parity from subtraction.
    ctx.ok(&.{ "query", "whereis", "std/peano-parity.bpa", "sub" },
        \\sub
        \\  std/peano-parity.bpa:19:  func sub = subtraction.sub
        \\  std/peano-subtraction.bpa:38:  func sub(a: Nat, b: Nat): Nat  [origin]
        \\
    );

    // an import namespace resolves to the imported file as its origin.
    ctx.ok(&.{ "query", "whereis", "std/peano-parity.bpa", "division" },
        \\division
        \\  std/peano-parity.bpa:10:  import division <<< "std/peano-division.bpa"
        \\  std/peano-division.bpa  [origin: imported file]
        \\
    );

    // an unknown identifier: located error, exit 1
    ctx.fail(&.{ "query", "whereis", "std/peano.bpa", "noSuchName" },
        \\noSuchName
        \\  error: no declaration named 'noSuchName' in std/peano.bpa
        \\
    );

    // `query search <file> <query>`: fuzzy match over theorem/axiom names +
    // statements. Both "cancel"-named decls match; ranked, one-line sigs.
    ctx.ok(&.{ "query", "search", "tests/cases/search_target.bpa", "cancel" },
        \\tests/cases/search_target.bpa:13:  axiom cancelAxiom: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
        \\tests/cases/search_target.bpa:16:  theorem addCancelLeft: forall c, a, b: Nat; add(c, a) = add(c, b) -> a = b
        \\
    );

    // no match: message + exit 1
    ctx.fail(&.{ "query", "search", "tests/cases/search_target.bpa", "zzznope" }, "no theorem or axiom matching 'zzznope'\n");
}
