//! The `model` accelerant (structure-reuse "X is-a Y"): transfers a source
//! theorem to the goal through a declared model's interpretation. Two modes
//! (MODEL-DESIGN.md): `--fast` trusts the transfer and taints `accelerated:
//! model`; the default (strict) MATERIALIZES the remapped source proof as a
//! synthetic kernel-checked theorem `Model$thm` (recursively for its cited
//! children), then cites it via `theorem_ref` — kernel-checked, untainted.
//! Split out of the elaborate monolith. The `models` field and the `model`
//! DECLARATION handler (`elaborateModel`) stay in elaborate.zig (decl-side);
//! the `Model`/`StmtPair` types stay there too (the field names them) and this
//! module references them as `Elaborator.Model`. The shared synthetic-theorem
//! primitives (begin/finish/wrapAsTheorem) stay as `pub` methods on Elaborator.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Model = Elaborator.Model;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

const std = @import("std");
const intern = @import("../intern.zig");
const StrId = intern.StrId;
const StatementId = @import("../env.zig").StatementId;

/// Two modes (MODEL-DESIGN.md):
///  - `--fast` (`!certify_arithmetic`): trust the transfer — taint
///    `accelerated: model`, check nothing about the source proof.
///  - default (strict): MATERIALIZE the source proof remapped as a synthetic
///    checked theorem `Model$thm` (recursively for its cited children), then
///    cite it via `theorem_ref` — kernel-checked, untainted.
pub fn justify(self: *Elaborator, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const inst_tok = c.schema orelse
        return self.fail(loc, "model requires an instance: model(<Instance>) <source.theorem>", .{});
    if (c.refs.len != 1) {
        return self.fail(loc, "model(<Instance>) cites exactly one source theorem; got {d}", .{c.refs.len});
    }
    const inst_name = try self.internTok(inst_tok);
    const model = self.models.getPtr(inst_name) orelse
        return self.fail(inst_tok.start, "unknown model '{s}'", .{self.text(inst_tok)});

    const stmt_id = try self.resolveStatementRef(c.refs[0]);
    const src_formula = switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
        .axiom => |f| f.formula,
        .theorem => |f| f.formula,
        .schema => return self.fail(c.refs[0].start, "model cannot transfer a schema; cite a plain axiom/theorem", .{}),
    };
    const transferred = self.pool.remapFormula(src_formula, model.remap) catch return error.OutOfMemory;
    if (!self.pool.alphaEq(transferred, goal)) {
        return self.fail(loc, "model transfer of '{s}' does not match the goal:\n  transferred: {s}\n  goal:        {s}", .{
            self.text(c.refs[0]),
            try self.renderTerm(transferred),
            try self.renderTerm(goal),
        });
    }

    if (!self.verify.certify_arithmetic) {
        // --fast: trust the transfer wholesale.
        const name = self.interner.intern("model") catch return error.OutOfMemory;
        try self.recordAccelerated(name, loc);
        return .{ .accelerated = name };
    }

    // strict: materialize the remapped source proof and cite it. Inherit the
    // materialized theorem's provenance (if the source proof leaned on an
    // accelerated tactic or a hole, the transfer discloses it transitively),
    // exactly like `fallback`.
    const mat_id = try materializeModelTheorem(self, model, stmt_id, c.refs[0].start);
    const mat = self.env.statements.items[@intFromEnum(mat_id)].theorem;
    try self.inheritAccelerated(mat.accelerated);
    try self.inheritHoles(mat.holes);
    return .{ .theorem_ref = .{ .stmt = mat_id, .loc = loc } };
}

/// Materialize a source theorem's proof, remapped through `model`, as a
/// synthetic kernel-checked theorem `Model$thm` in the current file — then
/// return its StatementId. Recursively materializes any source theorem the
/// proof cites (memoized per model, so a diamond emits once). Source axioms
/// cited by the proof are repointed through the model's `stmt_map` to their
/// discharging local facts; an unmapped axiom is an undischarged obligation.
fn materializeModelTheorem(self: *Elaborator, model: *Model, source: StatementId, loc: u32) ElabError!StatementId {
    if (model.materialized.get(source)) |existing| return existing;

    const stmt = self.env.statements.items[@intFromEnum(source)];
    const fact = switch (stmt) {
        .theorem => |t| t,
        .axiom => return self.fail(loc, "model materialization reached an axiom without a mapping; add it to the model", .{}),
        .schema => return self.fail(loc, "model cannot materialize a schema", .{}),
    };
    const proof = fact.proof orelse
        return self.fail(loc, "model cannot materialize '{s}': its proof was not retained (trusted import?)", .{self.interner.str(fact.name)});

    // mangled name `Model$sourcename`, bound in the current file. `$` is not
    // a lexable identifier char, so it cannot collide with a user name.
    const mangled = try mangledModelName(self, model.name, fact.name);
    const remapped_formula = self.pool.remapFormula(fact.formula, model.remap) catch return error.OutOfMemory;

    // register (unproven) FIRST so a self/mutual citation resolves; memoize
    // before recursing so a cycle terminates.
    const mat_id = try self.beginSyntheticTheorem(mangled, remapped_formula, loc);
    try model.materialized.put(self.arena, source, mat_id);

    // remap each step's formula + justification ids.
    const new_steps = try self.arena.alloc(kernel.Step, proof.steps.len);
    for (proof.steps, new_steps) |s, *out| {
        out.* = .{
            .formula = self.pool.remapFormula(s.formula, model.remap) catch return error.OutOfMemory,
            .just = try remapJustification(self, model, s.just, loc),
            .block = s.block,
            .label = s.label,
            .loc = loc,
        };
    }

    // remap each block's sort-bearing data: a `fix` eigenvariable's sort, an
    // `assume` formula, an `unpack` witness sort. (SRef/BRef indices and the
    // step ranges are structural — unchanged.)
    const new_blocks = try self.arena.alloc(kernel.Block, proof.blocks.len);
    for (proof.blocks, new_blocks) |b, *out| {
        out.* = b;
        out.kind = switch (b.kind) {
            .root => .root,
            .assume => |f| .{ .assume = self.pool.remapFormula(f, model.remap) catch return error.OutOfMemory },
            .fix => |v| .{ .fix = .{ .name = v.name, .sort = model.remap.sort(v.sort) } },
            .unpack => |u| .{ .unpack = .{
                .v = .{ .name = u.v.name, .sort = model.remap.sort(u.v.sort) },
                .source = u.source,
            } },
        };
    }

    // kernel-check the remapped proof, mark proven, retain it, and inherit the
    // source proof's provenance (accelerated/holes) — retention lets an OUTER
    // model re-materialize through this synthetic theorem (the multi-level
    // chain ℤ models ring models group).
    const on_fail = try std.fmt.allocPrint(self.arena, "model transfer of '{s}' does not kernel-check under the interpretation (an obligation is undischarged?)", .{self.interner.str(fact.name)});
    try self.finishSyntheticTheorem(mat_id, new_steps, new_blocks, fact.accelerated, fact.holes, loc, on_fail);
    return mat_id;
}

/// Remap a justification's embedded ids through the model: TermId fields via
/// remapFormula, StatementId fields (axiom/theorem refs) through the model's
/// mappings (axioms via `stmt_map`; theorems recursively materialized).
/// Intra-proof SRef/BRef indices are structural — unchanged.
fn remapJustification(self: *Elaborator, model: *Model, j: kernel.Justification, loc: u32) ElabError!kernel.Justification {
    return switch (j) {
        // a cited statement (axiom or theorem) in a materialized proof. The
        // citation rule (MODEL-DESIGN.md): it may cite the mapped target (in
        // the substitution list); an existing fact NOT affected by the
        // substitution (as-is, walk ends); or, for a source theorem affected
        // but unmapped, its recursive materialization. It may NOT cite a fact
        // that IS affected by the substitution but is absent from the mapping.
        .axiom_ref => |r| try remapCitation(self, model, r.stmt, false, loc),
        .theorem_ref => |r| try remapCitation(self, model, r.stmt, true, loc),
        .forall_elim => |r| .{ .forall_elim = .{
            .step = r.step,
            .with = self.pool.remapFormula(r.with, model.remap) catch return error.OutOfMemory,
            .with_loc = loc,
        } },
        .exists_intro => |r| .{ .exists_intro = .{
            .step = r.step,
            .witness = self.pool.remapFormula(r.witness, model.remap) catch return error.OutOfMemory,
            .witness_loc = loc,
        } },
        .schema_instance => |r| .{ .schema_instance = .{
            .instance = self.pool.remapFormula(r.instance, model.remap) catch return error.OutOfMemory,
            .premises = r.premises,
        } },
        // all other justifications carry only intra-proof SRef/BRef indices
        // (unchanged by the remap) or nothing.
        else => j,
    };
}

/// Repoint a cited statement (`source`, `is_theorem` = it was a theorem_ref)
/// through the model, per the materialization citation rule (MODEL-DESIGN.md):
///  - in the mapping  → cite the mapped target, kind-matched;
///  - not affected by the substitution → cite as-is, walk ends (its meaning
///    is unchanged by the interpretation);
///  - affected + a theorem → recursively materialize it;
///  - affected + an axiom, unmapped → FORBIDDEN (its meaning shifts under the
///    interpretation with nothing accounting for it) → error.
fn remapCitation(self: *Elaborator, model: *Model, source: StatementId, is_theorem: bool, loc: u32) ElabError!kernel.Justification {
    _ = is_theorem;
    // in the substitution list → cite the mapped target.
    for (model.stmt_map) |p| {
        if (p.from == source) return citeStatement(self, p.to, loc);
    }
    // not in the list: decide by whether the remap affects the fact.
    const stmt = self.env.statements.items[@intFromEnum(source)];
    const formula = switch (stmt) {
        .axiom => |f| f.formula,
        .theorem => |f| f.formula,
        .schema => return self.fail(loc, "model cannot transfer a proof citing a schema", .{}),
    };
    if (!model.remap.affects(self.pool, formula)) {
        // substitution-invariant: cite as-is, walk ends.
        return citeStatement(self, source, loc);
    }
    // affected but unmapped: a theorem is materialized; an axiom is forbidden.
    switch (stmt) {
        .theorem => {
            const mat = try materializeModelTheorem(self, model, source, loc);
            return .{ .theorem_ref = .{ .stmt = mat, .loc = loc } };
        },
        .axiom => |f| return self.fail(loc, "model materialization cites axiom '{s}', which the substitution affects but the model does not map; add a mapping for it", .{self.interner.str(f.name)}),
        .schema => unreachable,
    }
}

fn mangledModelName(self: *Elaborator, model_name: StrId, source_name: StrId) ElabError!StrId {
    const text_ = std.fmt.allocPrint(self.arena, "{s}${s}", .{
        self.interner.str(model_name), self.interner.str(source_name),
    }) catch return error.OutOfMemory;
    return self.interner.intern(text_) catch return error.OutOfMemory;
}

fn statementNameOf(self: *Elaborator, id: StatementId) StrId {
    return switch (self.env.statements.items[@intFromEnum(id)]) {
        .axiom => |f| f.name,
        .theorem => |f| f.name,
        .schema => |s| s.name,
    };
}

/// A citation of a statement by the justification matching its kind — so a
/// model obligation (an abstract axiom) discharged by a proven local theorem
/// cites it as `theorem_ref`, and one discharged by a local axiom as
/// `axiom_ref`. (A schema can't discharge an obligation — rejected earlier.)
fn citeStatement(self: *Elaborator, id: StatementId, loc: u32) kernel.Justification {
    return switch (self.env.statements.items[@intFromEnum(id)]) {
        .axiom => .{ .axiom_ref = .{ .stmt = id, .loc = loc } },
        .theorem => .{ .theorem_ref = .{ .stmt = id, .loc = loc } },
        .schema => .{ .axiom_ref = .{ .stmt = id, .loc = loc } }, // unreachable in practice
    };
}
