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
    const name_tok = c.schema.?; // parser guarantees presence for `specialize HEAD(...)`

    // The head may be a LOCAL STEP LABEL (a `forall`-shaped fact held in a proof
    // step) or a declared THEOREM/AXIOM name. Try the label FIRST — a local step
    // is already kernel-checked, so we cite its own SRef (no new cite step, no
    // taint inheritance) and seed the arg/hyp walk from it. Otherwise fall back to
    // the statement-name path.
    var cur: kernel.SRef = undefined;
    var cur_formula: TermId = undefined;
    const head_name = try self.internTok(name_tok);
    if (low.labels.get(head_name)) |target| {
        switch (target) {
            .step => |sid| {
                const s = low.steps.items[@intFromEnum(sid)];
                if (!Elaborator.lowAncestorOrSelf(low, s.block, block_id)) {
                    return self.fail(name_tok.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(name_tok)});
                }
                cur = .{ .id = sid, .loc = name_tok.start };
                cur_formula = s.formula;
            },
            .block => return self.fail(name_tok.start, "'{s}' names a subproof; a step is required", .{self.text(name_tok)}),
        }
    } else {
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
        // cite the theorem/axiom as a step to peel from (local steps skip this —
        // the step is already materialized).
        cur = try self.emitStep(low, block_id, name_tok.start, cited_formula, cite_just);
        cur_formula = cited_formula;
    }
    // Walk the cited formula by STRUCTURE, threading args and hyps in order: at a
    // `forall` consume the next arg (forall_elim); at a leading `->` consume the
    // next hyp (modus_ponens). This handles the interleaved guarded shape
    // `∀k; guard(k) -> ∀s,t; …` that a strict args-then-hyps split cannot — and
    // it is still just an emitted elim+mp chain the kernel re-checks (no trust
    // surface: the accelerant is only choosing the emission order).
    var ai: usize = 0; // next arg index
    var hi: usize = 0; // next hyp (ref) index
    while (ai < c.args.len or hi < c.refs.len) {
        // is this the FINAL consumption? If so, its justification is returned as
        // this step's own (no intermediate step emitted). Otherwise emit and advance.
        const is_last = (ai + 1 >= c.args.len) and (hi >= c.refs.len) or (ai >= c.args.len) and (hi + 1 >= c.refs.len);
        const node = self.pool.get(cur_formula);
        if (node == .quant and node.quant.q == .forall and ai < c.args.len) {
            const arg_expr = c.args[ai];
            ai += 1;
            const arg = try self.elaborateExpr(arg_expr);
            const opened = try self.pool.open(node.quant.body, arg.id);
            const j: kernel.Justification = .{ .forall_elim = .{ .step = cur, .with = arg.id, .with_loc = Elaborator.exprLoc(arg_expr) } };
            if (is_last) return j;
            cur = try self.emitStep(low, block_id, Elaborator.exprLoc(arg_expr), opened, j);
            cur_formula = opened;
        } else if (node == .bin and node.bin.op == .implies and hi < c.refs.len) {
            const ref = c.refs[hi];
            hi += 1;
            const ant = try self.resolveStepRef(low, ref);
            const j: kernel.Justification = .{ .modus_ponens = .{ .implication = cur, .antecedent = ant } };
            if (is_last) return j;
            cur = try self.emitStep(low, block_id, ref.start, node.bin.rhs, j);
            cur_formula = node.bin.rhs;
        } else {
            // structure doesn't match the remaining inputs.
            if (node == .quant and node.quant.q == .forall) {
                // a binder remains but only hyps left — a hyp can't skip a binder.
                return self.fail(c.refs[hi].start, "specialize: '{s}' is still universally quantified — supply an argument before this hypothesis", .{try self.renderTerm(cur_formula)});
            }
            if (ai < c.args.len) return self.fail(Elaborator.exprLoc(c.args[ai]), "specialize: '{s}' is not universally quantified here (too many arguments)", .{try self.renderTerm(cur_formula)});
            return self.fail(c.refs[hi].start, "specialize: no antecedent left to discharge for '{s}'", .{self.text(c.refs[hi])});
        }
    }
    // nothing consumed (bare `specialize THM`): the cite itself is the justification.
    return low.steps.items[@intFromEnum(cur.id)].just;
}
