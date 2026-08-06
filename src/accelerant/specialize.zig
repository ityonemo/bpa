//! The `specialize` accelerant: apply a `forall`-quantified THEOREM (or axiom) in
//! one written step. It substitutes for a chain of primitive steps — cite the
//! theorem, `forall_elim` at each argument (peeling the universal prefix), then
//! `modus_ponens` each hypothesis ref against a leading `->` antecedent — and
//! EMITS exactly those kernel steps as the certificate. So it is a genuine
//! multi-step accelerant, but a certificate-emitting one: the kernel re-checks the
//! emitted elim+mp chain, so no accelerated verdict is trusted and it carries no
//! `--fast` taint.
//!
//! It exists to collapse the ubiquitous three-step "apply a lemma" ritual
//! (`@rule [by theorem L]` / `@at-a [by forall_elim(a) rule]` / `@got [by
//! modus_ponens at-a hyp]`) into a single step. For a parameterized SCHEMA use
//! `instantiate` instead.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    _ = goal;
    const name_tok = c.schema.?; // parser guarantees presence for `specialize NAME(...)`
    const stmt_id = try self.resolveStatementRef(name_tok);
    const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
    const cited_formula: TermId, const cite_just: kernel.Justification = switch (stmt) {
        .axiom => |a| blk: {
            if (a.is_hole) try self.inheritHoles(a.holes);
            break :blk .{ a.formula, .{ .axiom_ref = .{ .stmt = stmt_id, .loc = name_tok.start } } };
        },
        .theorem => |t| blk: {
            try self.inheritAccelerated(t.accelerated);
            try self.inheritHoles(t.holes);
            break :blk .{ t.formula, .{ .theorem_ref = .{ .stmt = stmt_id, .loc = name_tok.start } } };
        },
        .schema => return self.fail(name_tok.start, "'{s}' is a schema; use `instantiate`", .{self.text(name_tok)}),
    };
    // cite the theorem as a step, then forall_elim at each arg (peeling the ∀
    // prefix — every arg but the last emits an intermediate step).
    var cur = try self.emitStep(low, block_id, name_tok.start, cited_formula, cite_just);
    var cur_formula = cited_formula;
    for (c.args) |arg_expr| {
        const node = self.pool.get(cur_formula);
        if (node != .quant or node.quant.q != .forall) {
            return self.fail(Elaborator.exprLoc(arg_expr), "specialize: '{s}' is not universally quantified here (too many arguments)", .{try self.renderTerm(cur_formula)});
        }
        const arg = try self.elaborateExpr(arg_expr);
        const opened = try self.pool.open(node.quant.body, arg.id);
        cur = try self.emitStep(low, block_id, Elaborator.exprLoc(arg_expr), opened, .{ .forall_elim = .{ .step = cur, .with = arg.id, .with_loc = Elaborator.exprLoc(arg_expr) } });
        cur_formula = opened;
    }
    // no hyps: the specialized formula IS the goal — return its cite/elim just.
    if (c.refs.len == 0) return low.steps.items[@intFromEnum(cur.id)].just;
    // modus_ponens each hypothesis ref against a leading `->` antecedent.
    for (c.refs, 0..) |ref, i| {
        const node = self.pool.get(cur_formula);
        if (node != .bin or node.bin.op != .implies) {
            return self.fail(ref.start, "specialize: no antecedent left to discharge for '{s}'", .{self.text(ref)});
        }
        const ant = try self.resolveStepRef(low, ref);
        const j: kernel.Justification = .{ .modus_ponens = .{ .implication = cur, .antecedent = ant } };
        if (i == c.refs.len - 1) return j; // last discharge = this step
        cur = try self.emitStep(low, block_id, ref.start, node.bin.rhs, j);
        cur_formula = node.bin.rhs;
    }
    unreachable;
}
