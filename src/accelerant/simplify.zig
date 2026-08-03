//! The `simplify` / `simplify_quantified` accelerant: prove an equation (or a
//! `forall …; s = t`) by rewriting both sides to a common normal form using the
//! cited facts as left-to-right rules. Certificate-ONLY (always emits kernel
//! steps; no `--fast` verdict). Split out of the elaborate monolith; the shared
//! rewrite/join substrate (`simplifyEquation`, `emitJoin`, the universal
//! open/close machinery) stays as `pub` methods on `Elaborator`.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

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
    return self.simplifyEquation(low, block_id, loc, c.refs, goal);
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
    const u = try self.peelUniversal(goal, "sq");
    if (self.pool.get(u.body) != .eq) {
        return self.fail(loc, "simplify_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
    }
    const opened = try self.openUniversal(low, block_id, u);
    const body_just = try self.simplifyEquation(low, opened.innermost, loc, c.refs, u.body);
    return self.closeUniversal(low, loc, u, opened.blocks, body_just);
}
