//! The `simplify` / `simplify_quantified` accelerant: prove an equation (or a
//! `forall …; s = t`) by rewriting both sides to a common normal form using the
//! cited facts as left-to-right rules. Certificate-ONLY (always emits kernel
//! steps; no `--fast` verdict).
//!
//! Strict-mode shape (Phase B): simplify's certificate is wrapped into a
//! CONTEXT-FREE synthetic theorem — one that cites NOTHING from the environment.
//! Every ref the tactic is handed (global axiom/theorem AND caller-local
//! hypothesis alike) becomes a PREMISE, and the eigenvariables the goal or those
//! premises mention become the ∀-prefix:
//!
//!     simplify$n :  ∀ <eigenvars> ;  P₁ -> P₂ -> … -> Pₖ -> <goal>
//!
//! Its proof is `fix <eigenvars> { assume P₁ { … assume Pₖ { <the rewrite
//! certificate, citing each Pᵢ as a local rule> } … } }`, closed by an
//! implies_intro chain (one per premise) then a forall_intro chain (one per
//! eigenvariable). At the cite site the closure is reversed: `theorem_ref` +
//! `forall_elim(<caller eigenvars>)` + one `modus_ponens` per premise,
//! discharging each Pᵢ with the SAME ref the tactic was handed (a global cited
//! as axiom_ref/theorem_ref, a local as the caller's step). The whole synthetic
//! theorem is kernel-checked (the soundness anchor in `wrapAsTheorem`).
//!
//! This all-refs-as-premises shape is simplify's OWN policy — other accelerants
//! choose differently (model transfers a closed statement; tautology/arithmetic
//! may pick another signature). Only the generic primitives (refTarget, the emit
//! / block machinery, wrapAsTheorem) live on the Elaborator.

const std = @import("std");
const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;
const StatementId = elaborate.StatementId;
const StrId = @import("../intern.zig").StrId;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const lexer = @import("../lexer.zig");
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
    return generate(self, low, block_id, loc, goal, c.refs);
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
    return generate(self, low, block_id, loc, goal, c.refs);
}

/// One cited fact, classified for closure: its formula (with the CALLER's
/// eigenvars), and how to discharge it at the cite (global → axiom/theorem ref;
/// local → the caller's step), plus the ref token (its name labels the surfaced
/// hypothesis step inside the synthetic proof so the certificate resolves it).
const Premise = struct {
    tok: lexer.Token,
    name: StrId,
    formula: TermId,
    target: Elaborator.RefTarget,
};

fn generate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, goal: TermId, refs: []const lexer.Token) ElabError!kernel.Justification {
    // classify every ref (in cite order) — each becomes a premise.
    var premises: std.ArrayList(Premise) = .empty;
    for (refs) |ref| {
        const t = try self.refTarget(low, block_id, ref);
        const formula = switch (t) {
            .local_step => |s| s.formula,
            .global => |g| g.formula,
        };
        try premises.append(self.arena, .{
            .tok = ref,
            .name = try self.internTok(ref),
            .formula = formula,
            .target = t,
        });
    }

    // eigenvariables the goal OR any premise mentions (scope order,
    // outermost-first). `.name` is the kernel fvar identity (keys close/
    // occursFree); `hint` keeps the user-facing name for display.
    var vars: std.ArrayList(term.Node.Fvar) = .empty;
    var hints: std.ArrayList(StrId) = .empty;
    for (self.scope.items) |entry| {
        var mentioned = self.pool.occursFree(goal, entry.fvar);
        if (!mentioned) for (premises.items) |p| {
            if (self.pool.occursFree(p.formula, entry.fvar)) {
                mentioned = true;
                break;
            }
        };
        if (mentioned) {
            try vars.append(self.arena, .{ .name = entry.fvar, .sort = entry.sort });
            try hints.append(self.arena, entry.name);
        }
    }

    // chain `P₁ -> … -> Pₖ -> goal` (fold from the right so cite order reads
    // outermost premise first), then ∀-close over the eigenvariables.
    var chain = goal;
    {
        var i = premises.items.len;
        while (i > 0) {
            i -= 1;
            chain = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = premises.items[i].formula, .rhs = chain } });
        }
    }
    var closed = chain;
    {
        var i = vars.items.len;
        while (i > 0) {
            i -= 1;
            const body = try self.pool.close(closed, vars.items[i].name);
            closed = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = vars.items[i].sort, .hint = hints.items[i], .body = body } });
        }
    }

    // ---- build the synthetic theorem's proof in a FRESH Lowering ----
    var plow: Lowering = .{};
    try plow.blocks.append(self.arena, .{
        .parent = null,
        .label = try self.interner.intern("proof"),
        .kind = .root,
        .first_step = 0,
        .last_step = 0,
    });
    const root: kernel.BlockId = @enumFromInt(0);

    // peel the ∀-prefix into fresh eigenvariables, one fix block each. Peeling
    // stops at the `->` chain (or the bare goal) — `u.body` is the fresh-eigenvar
    // implication chain.
    const u = try self.peelUniversal(closed, "simplify");
    const opened = try self.openUniversal(&plow, root, u);

    // one assume block per premise, surfacing each as a labeled hypothesis step
    // (under the ref's own name) so the certificate resolves it as a local rule.
    var parent = opened.innermost;
    var assume_blocks: std.ArrayList(kernel.BlockId) = .empty;
    var body_goal = u.body;
    for (premises.items) |p| {
        const node = self.pool.get(body_goal);
        std.debug.assert(node == .bin and node.bin.op == .implies);
        const ante = node.bin.lhs;
        const ab = try self.newBlock(&plow, try self.freshNamed("assume"), parent, .{ .assume = ante });
        _ = try registerLabeledHypothesis(self, &plow, ab, p.name, ante, loc);
        try assume_blocks.append(self.arena, ab);
        parent = ab;
        body_goal = node.bin.rhs;
    }

    // Build the rewrite cert for `body_goal` (citing each premise via the local
    // labels surfaced above). `body_goal` is a bare equation for `simplify`, or a
    // still-quantified `∀…; s = t` for `simplify_quantified` — emitBody handles
    // both (peeling+simplifying+closing in the quantified case). When there ARE
    // premises we emit the concluding step into the innermost assume block so the
    // implies_intro chain can reference it; when there are none, closeUniversal
    // emits the body itself (from `eq_just`) — emitting here too would duplicate.
    const eq_just = try emitBody(self, &plow, parent, loc, refs, body_goal);
    if (assume_blocks.items.len > 0) {
        _ = try self.emitStep(&plow, parent, loc, body_goal, eq_just);
    }

    // close the assume blocks with an implies_intro chain, innermost-first: each
    // implies_intro is emitted into its PARENT block and proves `Pᵢ -> <rest>`.
    // The OUTERMOST implies_intro (proving `u.body = P₁ -> … -> goal`) is not
    // emitted here — it is handed to closeUniversal as the fix-body justification
    // so it lands in the innermost fix block. `body_just` proves `u.body`.
    var body_just = eq_just;
    if (assume_blocks.items.len > 0) {
        var conclusion = body_goal;
        var bi = assume_blocks.items.len;
        while (bi > 0) {
            bi -= 1;
            const ab = assume_blocks.items[bi];
            self.closeBlock(&plow, ab);
            const assume_formula = plow.blocks.items[@intFromEnum(ab)].kind.assume;
            conclusion = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = assume_formula, .rhs = conclusion } });
            const ii: kernel.Justification = .{ .implies_intro = .{ .id = ab, .loc = loc } };
            if (bi == 0) {
                body_just = ii; // outermost — hand to closeUniversal
            } else {
                _ = try self.emitStep(&plow, assume_blocks.items[bi - 1], loc, conclusion, ii);
            }
        }
    }

    // close the fix blocks with forall_intro (closeUniversal emits the u.body
    // step into the innermost fix block and the forall_intro chain), then emit
    // the concluding root step proving `closed`.
    const proof_just = try self.closeUniversal(&plow, loc, u, opened.blocks, body_just);
    _ = try self.emitStep(&plow, root, loc, closed, proof_just);
    plow.blocks.items[0].last_step = @intCast(plow.steps.items.len);

    // wrap + kernel-check as a suppressed synthetic theorem.
    const name = try mangledName(self, "simplify");
    const accel = try self.arena.dupe(StrId, self.accelerated_used.items);
    const holes = try self.arena.dupe(StrId, self.holes_used.items);
    const thm = try self.wrapAsTheorem(name, closed, plow.steps.items, plow.blocks.items, accel, holes, loc, "simplify certificate does not kernel-check");

    // ---- cite it back in the caller: forall_elim(eigenvars) then a
    // modus_ponens per premise (discharge with the original refs) ----
    return emitCitation(self, low, block_id, loc, thm, closed, vars.items, premises.items);
}

/// Prove `body`, whichever shape remains after the ∀-prefix and premise chain
/// are peeled: a bare equation (`simplify`) runs `simplifyEquation` directly; a
/// still-quantified `∀…; s = t` (`simplify_quantified`) peels its binders into
/// fresh eigenvariables, simplifies the inner equation, and closes with
/// forall_intro. Returns a justification proving `body` in `block`.
fn emitBody(self: *Elaborator, low: *Lowering, block: kernel.BlockId, loc: u32, refs: []const lexer.Token, body: TermId) ElabError!kernel.Justification {
    if (self.pool.get(body) == .quant and self.pool.get(body).quant.q == .forall) {
        const u = try self.peelUniversal(body, "sq");
        const opened = try self.openUniversal(low, block, u);
        const inner = try self.simplifyEquation(low, opened.innermost, loc, refs, u.body);
        return self.closeUniversal(low, loc, u, opened.blocks, inner);
    }
    return self.simplifyEquation(low, block, loc, refs, body);
}

/// Surface `formula` as a `hypothesis` step in `block` (an assume block) and
/// register it under `name` so the certificate's ref lookups resolve it.
fn registerLabeledHypothesis(self: *Elaborator, low: *Lowering, block: kernel.BlockId, name: StrId, formula: TermId, loc: u32) ElabError!kernel.SRef {
    const id: kernel.StepId = @enumFromInt(low.steps.items.len);
    try low.steps.append(self.arena, .{
        .formula = formula,
        .just = .{ .hypothesis = .{ .id = block, .loc = loc } },
        .block = block,
        .label = name,
        .loc = loc,
    });
    try low.labels.put(self.arena, name, .{ .step = id });
    return .{ .id = id, .loc = loc };
}

/// Cite the synthetic theorem in the caller: `theorem_ref`, `forall_elim` per
/// eigenvariable (caller's real fvars), then `modus_ponens` per premise
/// (discharged by re-resolving each ref exactly as the dispatch would).
fn emitCitation(
    self: *Elaborator,
    low: *Lowering,
    block_id: kernel.BlockId,
    loc: u32,
    thm: StatementId,
    closed: TermId,
    vars: []const term.Node.Fvar,
    premises: []const Premise,
) ElabError!kernel.Justification {
    // The justification chain is: theorem_ref, then a forall_elim per eigenvar,
    // then a modus_ponens per premise. Each operation but the LAST is emitted as
    // its own step (so the next can reference it); the last is RETURNED as this
    // step's justification (the caller wraps it into the goal step). `pending`
    // holds the not-yet-emitted operation and the formula it would prove.
    var pending: kernel.Justification = .{ .theorem_ref = .{ .stmt = thm, .loc = loc } };
    var pending_formula = closed;
    // specialize the ∀-prefix at the caller's eigenvariables.
    for (vars) |v| {
        const prev = try self.emitStep(low, block_id, loc, pending_formula, pending);
        const q = self.pool.get(pending_formula).quant;
        const val = try self.pool.add(.{ .fvar = v });
        pending_formula = try self.pool.open(q.body, val);
        pending = .{ .forall_elim = .{ .step = prev, .with = val, .with_loc = loc } };
    }
    // discharge each premise with its original ref via modus_ponens.
    for (premises) |p| {
        const prev = try self.emitStep(low, block_id, loc, pending_formula, pending);
        const node = self.pool.get(pending_formula);
        std.debug.assert(node == .bin and node.bin.op == .implies);
        const ante_ref = try dischargeRef(self, low, block_id, loc, p);
        pending_formula = node.bin.rhs;
        pending = .{ .modus_ponens = .{ .implication = prev, .antecedent = ante_ref } };
    }
    // `pending` now proves the goal — return it as the step's justification.
    return pending;
}

/// Produce the step reference discharging a premise: a caller-local step is
/// cited directly; a global is materialized as an axiom_ref/theorem_ref step.
fn dischargeRef(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, p: Premise) ElabError!kernel.SRef {
    return switch (p.target) {
        .local_step => |s| s.sref,
        .global => |g| blk: {
            const just: kernel.Justification = if (g.is_theorem)
                .{ .theorem_ref = .{ .stmt = g.stmt, .loc = loc } }
            else
                .{ .axiom_ref = .{ .stmt = g.stmt, .loc = loc } };
            break :blk try self.emitStep(low, block_id, loc, g.formula, just);
        },
    };
}

fn mangledName(self: *Elaborator, tactic: []const u8) ElabError!StrId {
    self.fresh_counter += 1;
    const text_ = std.fmt.allocPrint(self.arena, "{s}${d}", .{ tactic, self.fresh_counter }) catch return error.OutOfMemory;
    return self.interner.intern(text_) catch return error.OutOfMemory;
}
