//! The `tautology` accelerant: closes a goal that is a propositional
//! consequence of its premises. The SMT engine (`smt_mod.tautology`) decides
//! validity; on `valid` the tactic first replays the truth search as ordinary
//! kernel steps (`tautologyCertificate` → `emitTautologyFrom`), staying
//! kernel-checked, and only falls back to the accelerated verdict when the
//! replay's step budget runs out. Split out of the elaborate monolith; the
//! shared propositional substrate (`emitTautologyFrom`, the `TautCert` struct)
//! stays as `pub` members on `Elaborator` — `ext` and the arithmetic mixed
//! certificate reuse them.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

const std = @import("std");
const smt_mod = @import("arithmetic/smt.zig");

const TautCert = Elaborator.TautCert;

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const premises = try self.resolvePremises(low, block_id, c, "tautology");
    const verdict = smt_mod.tautology(self.arena, self.pool, premises, goal) catch return error.OutOfMemory;
    switch (verdict) {
        .valid => {
            // certificate first: replay the truth search as ordinary
            // kernel steps — kernel-checked, no accelerated step
            if (try tautologyCertificate(self, low, block_id, goal, c)) |just| {
                return just;
            }
            // over budget: fall back to the accelerated verdict, marking
            // this use only
            const accelerated_name = self.interner.intern("tautology") catch return error.OutOfMemory;
            try self.recordAccelerated(accelerated_name, loc);
            return .{ .accelerated = accelerated_name };
        },
        .too_many_atoms => |n| {
            return self.fail(loc, "tautology: {d} distinct atoms exceeds the limit of {d}", .{ n, smt_mod.atom_limit });
        },
        .countermodel => |lits| {
            var msg: std.Io.Writer.Allocating = .init(self.arena);
            for (lits, 0..) |lit, i| {
                msg.writer.print("{s}{s} := {s}", .{
                    if (i > 0) ", " else "",
                    try self.renderTerm(lit.atom),
                    if (lit.value) "true" else "false",
                }) catch return error.OutOfMemory;
            }
            return self.fail(loc, "tautology: not a propositional consequence; countermodel: {s}", .{msg.written()});
        },
    }
}

// --- B2: tautology certificates -----------------------------------------
// Replays the truth search as ordinary kernel steps: each split atom gets
// an inline excluded-middle (the 9-step or_intro/not_intro/
// double_negation shape) and an or_elim over the two assumption branches;
// leaves either derive the goal structurally from the literal
// assumptions (trueJust/falseJust) or explode a refuted premise with
// absurd. The kernel checks every step, so this path stays kernel-checked. A
// step budget bounds the exponential replay; past it the synthesized
// steps roll back and the caller falls back to the accelerated path.

/// Attempt a certificate for a goal the engine already decided valid.
/// Returns null (with no steps emitted) when the budget runs out.
fn tautologyCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!?kernel.Justification {
    const loc = c.rule.start;
    const steps_mark = low.steps.items.len;
    const blocks_mark = low.blocks.items.len;

    // premise steps: label refs are already steps; statement refs get a
    // citation step emitted (accessibility and proven-ness were checked
    // by resolvePremises)
    const premise_steps = try self.arena.alloc(TautCert.Premise, c.refs.len);
    for (c.refs, premise_steps) |ref, *out| {
        const name = try self.internTok(ref);
        if (low.labels.get(name)) |target| {
            const sid = target.step; // resolvePremises rejected blocks
            out.* = .{
                .formula = low.steps.items[@intFromEnum(sid)].formula,
                .ref = .{ .id = sid, .loc = ref.start },
            };
        } else {
            const stmt_id = try self.resolveStatementRef(ref);
            const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
            out.* = switch (stmt) {
                .axiom => |a| .{
                    .formula = a.formula,
                    .ref = try self.emitStep(low, block_id, loc, a.formula, .{ .axiom_ref = .{ .stmt = stmt_id, .loc = loc } }),
                },
                .theorem => |t| .{
                    .formula = t.formula,
                    .ref = try self.emitStep(low, block_id, loc, t.formula, .{ .theorem_ref = .{ .stmt = stmt_id, .loc = loc } }),
                },
                .schema => unreachable, // resolvePremises rejected these
            };
        }
    }

    return self.emitTautologyFrom(low, block_id, goal, premise_steps, loc, steps_mark, blocks_mark);
}
