//! Integration gates — multi-file checking: import resolution, the trust model, and the --fast/--faster/--reckless speed flags.
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

    // directory boundaries: subdir import chaining to a parent-dir import
    ctx.okSilent(&.{ "check", "tests/cases/imports/chain.bpa" });

    // diamond imports + re-export: one lib, two hops, same entities
    ctx.okSilent(&.{ "check", "tests/cases/imports/diamond.bpa" });

    // guards travel across imports
    ctx.fail(&.{ "check", "tests/cases/imports/guarded_bad.bpa" }, "tests/cases/imports/guarded_bad.bpa:4:14: error: unproved obligation: 'Z != Z'\n");

    // a missing import file is a clean diagnostic at the import site
    ctx.fail(&.{ "check", "tests/cases/imports/missing_import.bpa" }, "tests/cases/imports/missing_import.bpa:2:18: error: cannot open 'tests/cases/imports/nope.bpa': file not found\n");

    // a namespace name collides with a local declaration
    ctx.fail(&.{ "check", "tests/cases/imports/collide.bpa" }, "tests/cases/imports/collide.bpa:3:8: error: duplicate declaration of 'lib'\n");

    // --faster trusts imported proofs (peano-imports imports peano.bpa,
    // whose one accelerated step would otherwise be re-checked and hard-error).
    ctx.ok(&.{ "check", "--faster", "examples/peano-imports.bpa" },
        \\OK: 24 declarations, 1 theorems proven, 6 imported theorems trusted
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates imported-proofs); re-run `bpa check` to elaborate.
        \\
    );

    // --fast re-checks the imported proofs; since Cooper-replay certifies the
    // once-accelerated evenOrOdd, nothing is deferred and all seven are elaborated (the
    // --fast banner still fires).
    ctx.ok(&.{ "check", "--fast", "examples/peano-imports.bpa" },
        \\OK: 24 declarations, 7 theorems proven
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates); re-run `bpa check` to elaborate.
        \\
    );

    // trust semantics: importing an INCORRECT theorem passes under --faster
    // (imported proofs trusted)...
    ctx.ok(&.{ "check", "--faster", "tests/cases/imports/trusts_broken.bpa" },
        \\OK: 7 declarations, 1 theorems proven, 1 imported theorems trusted
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates imported-proofs); re-run `bpa check` to elaborate.
        \\
    );

    // ...and is caught by the DEFAULT (imported proofs re-checked),
    // poisoning its citations downstream
    ctx.fail(&.{ "check", "tests/cases/imports/trusts_broken.bpa" },
        \\tests/cases/imports/trusts_broken.bpa:8:17: error: cites unproven theorem 'aIsB'
        \\tests/cases/imports/broken_lib.bpa:9:4: error: proof concludes 'A = A' but the theorem states 'A = B'
        \\
    );

    // --reckless additionally trusts imported schemas (banner names all
    // three deferred layers)
    ctx.ok(&.{ "check", "--reckless", "examples/peano-imports.bpa" },
        \\OK: 24 declarations, 1 theorems proven, 6 imported theorems trusted
        \\  — ACCELERATED (results trusted from the procedure, not elaborated to kernel steps; not elaborated: arithmetic-certificates imported-proofs imported-schemas); re-run `bpa check` to elaborate.
        \\
    );

    // at most one speed flag
    ctx.fail(&.{ "check", "--fast", "--reckless", "examples/peano-imports.bpa" }, "error: at most one of --fast / --faster / --reckless\n");

    ctx.okSilent(&.{ "check", "tests/cases/imports/uses.bpa" });

    // Imports, broken siblings (messages pinned once implemented)
    ctx.fail(&.{ "check", "tests/cases/imports/cycle_a.bpa" }, "tests/cases/imports/cycle_b.bpa:2:14: error: import cycle detected via 'tests/cases/imports/cycle_a.bpa'\n");

    ctx.fail(&.{ "check", "tests/cases/imports/bad_alias.bpa" }, "tests/cases/imports/bad_alias.bpa:3:14: error: 'lib.NIL' is not a sort\n");

    ctx.fail(&.{ "check", "tests/cases/imports/unknown_ns.bpa" }, "tests/cases/imports/unknown_ns.bpa:3:10: error: unknown namespace 'ghost'\n");
}
