//! The `chain` accelerant (module `chain`): prove an equality goal `A = Z`
//! from a bag of cited equations used in ANY direction, closed under congruence.
//!
//! Where `simplify` orients each cited equation left-to-right and reduces both
//! sides to a normal form (and fails when the equations must be used in
//! conflicting directions), `chain` treats each cited `X = Y` as an
//! undirected edge and does a breadth-first search for a rewrite path connecting
//! `A` to `Z`. Because the kernel `rewrite` rule already rewrites congruent
//! SUBTERMS, applying an equation `p = q` (or its `symmetry` flip `q = p`)
//! rewrites every occurrence of `p` — so congruence (`a = b ⟹ f(…a…) = f(…b…)`)
//! falls out for free.
//!
//! Two-phase: SEARCH the path purely (no steps emitted), then EMIT it as
//! `reflexivity` + optional `symmetry` (flip a cited equation) + `rewrite` steps
//! the kernel re-checks — certificate-emitting, no `--fast` taint.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

const std = @import("std");

/// A cited equation, resolved to a proof step plus its two sides.
const Equation = struct { step: kernel.SRef, lhs: TermId, rhs: TermId };

/// One edge of the found path: rewrite `from`→`to` in the running term using
/// `eq_idx`'s equation in the given orientation (`forward` = lhs→rhs).
const Edge = struct { eq_idx: usize, forward: bool, result: TermId };

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const gnode = self.pool.get(goal);
    if (gnode != .eq) {
        return self.fail(loc, "chain proves an equation 'A = Z'; the goal is '{s}'", .{try self.renderTerm(goal)});
    }
    const start = gnode.eq.lhs;
    const target = gnode.eq.rhs;

    if (c.refs.len == 0) return self.fail(loc, "chain needs at least one cited equation", .{});
    const eqs = try self.arena.alloc(Equation, c.refs.len);
    for (c.refs, eqs) |ref, *e| {
        const s = try self.resolveStepRef(low, ref);
        const n = self.pool.get(low.steps.items[@intFromEnum(s.id)].formula);
        if (n != .eq) return self.fail(ref.start, "chain: '{s}' is not an equation", .{self.text(ref)});
        e.* = .{ .step = s, .lhs = n.eq.lhs, .rhs = n.eq.rhs };
    }

    // PHASE 1 — BFS from `start` to `target`, recording the edge into each term.
    // `came_from` maps a discovered term to the Edge that produced it.
    // `came_from` maps a discovered term to the Edge into it. `start` is NOT in
    // the map (it has no incoming edge); a separate `seen` set marks visited.
    var came_from: std.AutoHashMapUnmanaged(TermId, Edge) = .empty;
    var seen: std.AutoHashMapUnmanaged(TermId, void) = .empty;
    var queue: std.ArrayList(TermId) = .empty;
    try queue.append(self.arena, start);
    try seen.put(self.arena, start, {});
    var head: usize = 0;
    const cap = 4096; // node budget — congruence-free equational chains are tiny
    var found = self.pool.alphaEq(start, target);
    while (head < queue.items.len and !found and seen.count() < cap) {
        const curterm = queue.items[head];
        head += 1;
        for (eqs, 0..) |e, ei| {
            for ([_]bool{ true, false }) |forward| {
                const from = if (forward) e.lhs else e.rhs;
                const to = if (forward) e.rhs else e.lhs;
                const raw = try self.pool.rewriteAll(curterm, from, to);
                if (self.pool.alphaEq(raw, curterm)) continue; // no change
                // The pool is not hash-consed: two structurally-equal terms have
                // DIFFERENT TermIds, so a by-id `seen` set would miss reconvergence
                // (and mis-key the target). Canonicalize `raw` to an already-seen
                // id when alpha-equal — target first (the common case), then the
                // rest of the frontier.
                var nxt = raw;
                if (self.pool.alphaEq(raw, target)) {
                    nxt = target;
                } else {
                    var it = seen.keyIterator();
                    while (it.next()) |k| {
                        if (self.pool.alphaEq(raw, k.*)) {
                            nxt = k.*;
                            break;
                        }
                    }
                }
                if (seen.get(nxt) != null) continue; // already reached
                try seen.put(self.arena, nxt, {});
                try came_from.put(self.arena, nxt, .{ .eq_idx = ei, .forward = forward, .result = curterm });
                try queue.append(self.arena, nxt);
                if (self.pool.alphaEq(nxt, target)) {
                    found = true;
                    break;
                }
            }
            if (found) break;
        }
    }
    if (!found) {
        return self.fail(loc, "chain: cannot connect '{s}' to '{s}' from the cited equations", .{ try self.renderTerm(start), try self.renderTerm(target) });
    }

    // reconstruct the path start → target (list of terms, target last).
    var path: std.ArrayList(TermId) = .empty;
    {
        var t = target;
        while (!self.pool.alphaEq(t, start)) {
            try path.append(self.arena, t);
            const edge = came_from.get(t) orelse return self.fail(loc, "chain: internal path reconstruction failed at '{s}'", .{try self.renderTerm(t)});
            t = edge.result;
        }
    }
    // path is target-first; reverse to walk start → … → target.
    std.mem.reverse(TermId, path.items);

    // PHASE 2 — emit: reflexivity `start = start`, then one rewrite per path edge.
    const refl = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = start } });
    var cur_step = try self.emitStep(low, block_id, loc, refl, .reflexivity);
    for (path.items, 0..) |next_term, i| {
        const edge = came_from.get(next_term).?;
        const e = eqs[edge.eq_idx];
        // the equation step to cite, flipped by symmetry when used backward.
        const eq_step = if (edge.forward)
            e.step
        else
            try self.emitStep(low, block_id, loc, try self.pool.add(.{ .eq = .{ .lhs = e.rhs, .rhs = e.lhs } }), .{ .symmetry = e.step });
        const new_goal = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = next_term } });
        const j: kernel.Justification = .{ .rewrite = .{ .equation = eq_step, .target = cur_step } };
        if (i == path.items.len - 1) return j; // last edge → this step's justification
        cur_step = try self.emitStep(low, block_id, loc, new_goal, j);
    }
    // path empty only when start ≡ target; then reflexivity IS the proof.
    return low.steps.items[@intFromEnum(cur_step.id)].just;
}
