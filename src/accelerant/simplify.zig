//! The `simplify` / `simplify_quantified` accelerant: prove an equation (or a
//! `forall …; s = t`) by rewriting both sides to a common normal form using the
//! cited facts as left-to-right rules. Certificate-ONLY (always emits kernel
//! steps; no `--fast` verdict).
//!
//! Strict-mode shape (Phase B): simplify closes ALL its refs as premises of a
//! context-free synthetic theorem (see `_common.zig`), so it handles refs that
//! resolve to caller-local hypotheses (e.g. an inductive hypothesis) as well as
//! globals. The shared `_common.generate` does the wrap + cite; simplify only
//! supplies the tactic name, the refs to close (all of them), and the body-emit
//! (the rewrite/join core).

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const lexer = @import("../lexer.zig");
const term = @import("../term.zig");
const TermId = term.TermId;
const common = @import("_common.zig");

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .eq) {
        // a forall over an equation is the common mistake — point at the tactic
        // that handles it
        if (goal_node == .quant and goal_node.quant.q == .forall) {
            return self.fail(loc, "simplify proves equations; did you mean simplify_quantified?", .{});
        }
        return self.fail(loc, "simplify proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
    }
    var body: EqBody = .{ .refs = c.refs, .loc = loc };
    return common.generate(self, low, block_id, loc, "simplify", goal, c.refs, &body);
}

pub fn justifyQuantified(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .quant or goal_node.quant.q != .forall) {
        if (goal_node == .eq) {
            return self.fail(loc, "simplify_quantified expects a quantified goal; did you mean simplify?", .{});
        }
        return self.fail(loc, "simplify_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
    }
    // validate the shape up front (the synthetic proof would fail anyway, but
    // this gives the precise "body is not an equation" diagnostic).
    const u = try self.peelUniversal(goal, "sq");
    if (self.pool.get(u.body) != .eq) {
        return self.fail(loc, "simplify_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
    }
    var body: EqBody = .{ .refs = c.refs, .loc = loc };
    return common.generate(self, low, block_id, loc, "simplify", goal, c.refs, &body);
}

/// The body-emit for simplify's closure: prove the (fresh-eigenvar) equation via
/// the rewrite/join core, citing each premise through the local labels the
/// closure surfaced. A still-quantified `∀…; s = t` body (from
/// simplify_quantified) is peeled and closed here.
const EqBody = struct {
    refs: []const lexer.Token,
    loc: u32,
    pub fn emit(b: *EqBody, self: *Elaborator, low: *Lowering, block: kernel.BlockId, body_goal: TermId) ElabError!kernel.Justification {
        if (self.pool.get(body_goal) == .quant and self.pool.get(body_goal).quant.q == .forall) {
            const u = try self.peelUniversal(body_goal, "sq");
            const opened = try self.openUniversal(low, block, u);
            const inner = try self.simplifyEquation(low, opened.innermost, b.loc, b.refs, u.body);
            return self.closeUniversal(low, b.loc, u, opened.blocks, inner);
        }
        return self.simplifyEquation(low, block, b.loc, b.refs, body_goal);
    }
};
