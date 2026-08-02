//! Elaboration: surface AST -> kernel terms. Resolves names, checks sorts,
//! stores declarations in the Env. Schemas are stored as forms, NOT
//! elaborated (comptime semantics: checked per instantiation, in M4).
//!
//! Untrusted machinery: nothing here establishes a theorem; it only prepares
//! concrete terms for the kernel and rejects ill-formed input early with
//! precise diagnostics.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("ast.zig");
const lexer = @import("lexer.zig");
const intern = @import("intern.zig");
const StrId = intern.StrId;
const term = @import("term.zig");
const SortId = term.SortId;
const TermId = term.TermId;
const Env = @import("env.zig").Env;
const FileId = @import("env.zig").FileId;
const Symbol = @import("env.zig").Symbol;
const Statement = @import("env.zig").Statement;
const StatementId = @import("env.zig").StatementId;
const Diagnostics = @import("diagnostics.zig");
const kernel = @import("kernel.zig");
const simplify_mod = @import("simplify.zig");
const smt_mod = @import("smt.zig");
const presburger_mod = @import("presburger.zig");
const farkas_mod = @import("farkas.zig");

const ElabError = error{ Recover, OutOfMemory };

/// What to actually verify, as independent knobs. Full verification (all true)
/// is the default; the CLI's `--fast`/`--faster`/`--reckless` flags are
/// monotonic presets that turn these off one at a time to speed up the
/// edit→check loop during development (always loudly disclosed). Modeled as
/// separate booleans, not a flat enum, so a future per-project manifest and
/// verification cache address the same knobs without rework.
pub const Verify = struct {
    /// `by arithmetic`/`by tautology` must produce a checkable certificate
    /// (elaborated to kernel steps); an accelerated fallback is a hard error.
    /// When false, take the accelerated verdict and record it (disclosed in the
    /// summary).
    certify_arithmetic: bool = true,
    /// re-check imported theorems' proofs. When false, imported theorem bodies
    /// are trusted (declarations load, proofs are not re-verified).
    recheck_imports: bool = true,
    /// re-check imported schemas at each instantiation. When false, a proven
    /// imported schema is trusted without re-instantiating its body.
    recheck_schemas: bool = true,
};

pub const Elaborator = struct {
    arena: Allocator,
    source: []const u8,
    interner: *intern.Interner,
    pool: *term.Pool,
    env: *Env,
    sink: *Diagnostics.Sink,
    /// the file being elaborated: all unqualified names resolve in its scope
    file: FileId,
    /// the scope well-known ARITHMETIC names (symbols + lemmas) resolve in.
    /// Null means "local scope" (self.file) — bare `by arithmetic`, today's
    /// behavior. Set to a named theory module's FileId for `arithmetic(<mod>)`
    /// so the certifiers resolve roles against that theory regardless of local
    /// aliases. Scoped: set at the top of arithmeticJustification, restored
    /// after.
    theory_file: ?FileId = null,
    /// raw import path (as written, interned) -> loaded file, from the loader
    imports: ?*const std.AutoHashMapUnmanaged(StrId, FileId) = null,
    /// trusted mode (imported files without --recursive): declarations are
    /// elaborated but proofs are NOT checked and obligations are NOT owed;
    /// theorems are marked proven-by-trust. Schema proofs are unaffected —
    /// they are always re-checked at instantiation, in the instantiating
    /// file's (untrusted) elaboration.
    trusted: bool = false,
    /// which layers to verify (see `Verify`). Default: verify everything.
    verify: Verify = .{},
    /// accelerated-tactic names the CURRENT top-level theorem's proof has
    /// leaned on (directly, or transitively via citations and schema
    /// re-checks); cleared per theorem, stored on the fact when it proves
    accelerated_used: std.ArrayList(StrId) = .empty,
    /// hole names the CURRENT top-level theorem's proof rests on (a cited hole,
    /// or a cited theorem that itself rests on holes); cleared per theorem,
    /// stored on the fact when it proves. Same accumulate-then-store shape as
    /// accelerated_used.
    holes_used: std.ArrayList(StrId) = .empty,
    /// innermost binding last: quantifier binders, proof vars, func params
    scope: std.ArrayList(ScopeEntry) = .empty,
    /// generator for hygienic binder fvar names ('#' cannot lex, so these can
    /// never collide with user identifiers)
    fresh_counter: u32 = 0,
    /// set while elaborating a schema body/proof: param name -> argument
    schema_args: ?*const SchemaArgs = null,
    /// schemas currently being instantiated, innermost last. A StatementId
    /// already on the stack means the schema (transitively) instantiates
    /// itself — a genuine cycle, reported as such. Depth is otherwise
    /// unbounded for terminating chains (only a huge backstop guards memory).
    instantiating: std.ArrayList(StatementId) = .empty,
    /// the file's forward manifest: names promised to be theorems, checked
    /// for existence and kind once the whole file has elaborated
    forwards: std.ArrayList(struct { name: StrId, loc: u32, text: []const u8 }) = .empty,
    /// proof obligations (TCCs) from guarded-function applications, emitted at
    /// the application and wrapped in logical context (binders, antecedents,
    /// left conjuncts) as elaboration returns upward. Discharged at the
    /// enclosing statement/step; an undischarged obligation fails the check.
    pending_tccs: std.ArrayList(Tcc) = .empty,

    /// declared `model`s, keyed by instance name. A cite `[by model(Name) thm]`
    /// looks the model up here and remaps `thm`'s formula through its `Remap`.
    models: std.AutoHashMapUnmanaged(StrId, Model) = .empty,

    const Tcc = struct { formula: TermId, loc: u32 };

    /// A resolved `model` declaration: the interpretation (`remap`) plus the
    /// source theory's file (to resolve cited source theorems at their origin)
    /// and a location for diagnostics. Owned slices live in the arena.
    const Model = struct {
        remap: term.Pool.Remap,
        source_file: FileId,
        loc: u32,
    };

    const ScopeEntry = struct {
        /// user-facing name (what source text resolves against)
        name: StrId,
        sort: SortId,
        /// fvar identity in kernel terms: fresh for quantifier binders
        /// (closed away immediately), the user name for proof vars and params
        fvar: StrId,
    };

    pub const SchemaArgs = std.AutoHashMapUnmanaged(StrId, SchemaArg);
    pub const SchemaArg = union(enum) {
        value: Typed,
        /// single-argument generator: body has one loose bvar
        lambda: struct { body: TermId, arg_sort: SortId, result_sort: SortId },
    };

    pub const Typed = struct { id: TermId, sort: SortId };

    pub fn init(
        arena: Allocator,
        source: []const u8,
        interner: *intern.Interner,
        pool: *term.Pool,
        env: *Env,
        sink: *Diagnostics.Sink,
        file: FileId,
    ) Elaborator {
        return .{
            .arena = arena,
            .source = source,
            .interner = interner,
            .pool = pool,
            .env = env,
            .sink = sink,
            .file = file,
        };
    }

    fn text(self: *const Elaborator, tok: lexer.Token) []const u8 {
        return self.source[tok.start..tok.end];
    }

    fn internTok(self: *Elaborator, tok: lexer.Token) !StrId {
        return self.interner.intern(self.text(tok));
    }

    fn fail(self: *Elaborator, offset: u32, comptime fmt: []const u8, args: anytype) ElabError {
        self.sink.add(offset, fmt, args) catch return error.OutOfMemory;
        return error.Recover;
    }

    fn sortName(self: *const Elaborator, id: SortId) []const u8 {
        return self.env.sortName(self.interner, id);
    }

    pub fn elaborateFile(self: *Elaborator, file: ast.File) !void {
        for (file.decls) |*decl| {
            self.elaborateDecl(decl) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => continue, // diagnostic already recorded
            };
        }
        // verify the forward manifest: every promised theorem must now exist
        for (self.forwards.items) |fwd| {
            const stmt = self.env.findStatement(self.file, fwd.name) orelse {
                self.sink.add(fwd.loc, "forwarded theorem '{s}' is never defined", .{fwd.text}) catch return error.OutOfMemory;
                continue;
            };
            const kind_name: ?[]const u8 = switch (stmt.*) {
                .theorem => null, // ok
                .schema => |s| if (s.proof != null) null else "a parameterized axiom",
                .axiom => "an axiom",
            };
            if (kind_name) |k| {
                self.sink.add(fwd.loc, "'{s}' is forwarded as a theorem but defined as {s}", .{ fwd.text, k }) catch return error.OutOfMemory;
            }
        }
    }

    fn elaborateDecl(self: *Elaborator, decl: *const ast.Decl) ElabError!void {
        std.debug.assert(self.scope.items.len == 0);
        defer self.scope.clearRetainingCapacity();
        // obligations never survive a declaration (error paths may leave some)
        defer self.pending_tccs.clearRetainingCapacity();
        switch (decl.*) {
            .forward => |d| {
                try self.forwards.append(self.arena, .{
                    .name = try self.internTok(d.name),
                    .loc = d.name.start,
                    .text = self.text(d.name),
                });
            },
            .import => |d| {
                const name = try self.internTok(d.ns);
                try self.checkFreshName(name, d.ns);
                const path_text = self.text(d.path);
                const raw = self.interner.intern(path_text[1 .. path_text.len - 1]) catch return error.OutOfMemory;
                // the loader resolved (and diagnosed) imports; a missing entry
                // means it already reported — stay silent here
                const target = if (self.imports) |m| m.get(raw) else null;
                if (target) |t| try self.env.addNamespace(self.file, name, t);
            },
            .alias => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const target = try self.resolveTarget(d.target);
                switch (d.kind) {
                    .sort => {
                        const id = self.env.findSort(target.file, target.base) orelse
                            return self.fail(d.target.start, "'{s}' is not a sort", .{self.text(d.target)});
                        try self.env.registerSort(self.file, name, id);
                    },
                    .constant, .func, .pred => {
                        const id = self.env.findSym(target.file, target.base) orelse
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        const sym = self.env.sym(id);
                        const ok = switch (d.kind) {
                            .constant => sym.kind == .app and sym.arg_sorts.len == 0,
                            .func => sym.kind == .app,
                            .pred => sym.kind == .pred,
                            else => unreachable,
                        };
                        if (!ok) {
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        }
                        try self.env.registerSym(self.file, name, id);
                    },
                    .axiom, .theorem => {
                        const id = self.env.findStatementId(target.file, target.base) orelse
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        const stmt = self.env.statements.items[@intFromEnum(id)];
                        // parameterized statements (schemas) alias under the
                        // keyword matching their epistemic kind
                        const ok = switch (d.kind) {
                            .axiom => stmt == .axiom or (stmt == .schema and stmt.schema.proof == null),
                            .theorem => stmt == .theorem or (stmt == .schema and stmt.schema.proof != null),
                            else => unreachable,
                        };
                        if (!ok) {
                            return self.fail(d.target.start, "'{s}' is not a {s}", .{ self.text(d.target), @tagName(d.kind) });
                        }
                        try self.env.registerStatement(self.file, name, id);
                    },
                }
            },
            .sort => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                _ = try self.env.addSort(self.file, name, d.name.start);
            },
            .constant => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const sort = try self.resolveSort(d.sort);
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = .app,
                    .arg_sorts = &.{},
                    .result = sort,
                    .guard = null,
                    .param_names = &.{},
                    .loc = d.name.start,
                });
            },
            .define => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const tcc_start = self.pending_tccs.items.len;
                const value = try self.elaborateExpr(d.value);
                // guards inside the definition are owed once, here; uses
                // expand to the already-vetted term
                try self.dischargeTccs(null, @enumFromInt(0), tcc_start);
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = .app,
                    .arg_sorts = &.{},
                    .result = value.sort,
                    .guard = null,
                    .definition = value.id,
                    .param_names = &.{},
                    .loc = d.name.start,
                });
            },
            .func => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const arg_sorts, const param_names = try self.resolveParams(d.params);
                const result = try self.resolveSort(d.result);
                if (result == .prop) {
                    return self.fail(d.result.start, "a func cannot return 'Prop'; declare a pred instead", .{});
                }
                var guard: ?TermId = null;
                if (d.requires) |req| {
                    // params in scope as fvars named after themselves
                    for (param_names, arg_sorts) |pn, ps| {
                        try self.scope.append(self.arena, .{ .name = pn, .sort = ps, .fvar = pn });
                    }
                    const tcc_start = self.pending_tccs.items.len;
                    const g = try self.elaborateExpr(req);
                    // guards must be guard-free, or obligations regress
                    if (self.pending_tccs.items.len > tcc_start) {
                        return self.fail(self.pending_tccs.items[tcc_start].loc, "a 'requires' clause may only mention total functions", .{});
                    }
                    guard = (try self.requireProp(g, req)).id;
                    self.scope.clearRetainingCapacity();
                }
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = .app,
                    .arg_sorts = arg_sorts,
                    .result = result,
                    .guard = guard,
                    .param_names = param_names,
                    .loc = d.name.start,
                });
            },
            .pred => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const arg_sorts, const param_names = try self.resolveParams(d.params);
                _ = try self.env.addSym(self.file, .{
                    .name = name,
                    .kind = .pred,
                    .arg_sorts = arg_sorts,
                    .result = .prop,
                    .guard = null,
                    .param_names = param_names,
                    .loc = d.name.start,
                });
            },
            .axiom => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const f = try self.elaborateExpr(d.formula);
                const typed = try self.requireProp(f, d.formula);
                // an axiom with unproved guard obligations must not enter the
                // environment: it would smuggle in unguarded applications
                try self.dischargeTccs(null, @enumFromInt(0), 0);
                _ = try self.env.addStatement(self.file, name, .{ .axiom = .{
                    .name = name,
                    .formula = typed.id,
                    .loc = d.name.start,
                } });
            },
            .hole => |d| {
                // mechanically an axiom, but marked a hole: default mode rejects
                // any proof that (transitively) rests on it; --draft allows it.
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const f = try self.elaborateExpr(d.formula);
                const typed = try self.requireProp(f, d.formula);
                try self.dischargeTccs(null, @enumFromInt(0), 0);
                _ = try self.env.addStatement(self.file, name, .{ .axiom = .{
                    .name = name,
                    .formula = typed.id,
                    .loc = d.name.start,
                    .is_hole = true,
                    .holes = try self.arena.dupe(StrId, &.{name}),
                } });
            },
            .schema => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                // lazy (comptime semantics): validate only the parameter
                // signature; the body is checked per instantiation.
                for (d.params) |p| {
                    try self.checkNoShadow(try self.internTok(p.name), p.name);
                    for (p.arg_sorts) |s| _ = try self.resolveSort(s);
                    _ = try self.resolveSort(p.result);
                }
                _ = try self.env.addStatement(self.file, name, .{ .schema = .{
                    .name = name,
                    .params = d.params,
                    .body = d.formula,
                    .proof = d.steps,
                    .file = self.file,
                    .source = self.source,
                    .loc = d.name.start,
                } });
            },
            .theorem => |d| {
                const name = try self.internTok(d.name);
                try self.checkFreshName(name, d.name);
                const f = try self.elaborateExpr(d.formula);
                const typed = try self.requireProp(f, d.formula);
                // the statement's own guard obligations must match a prior
                // axiom or proven theorem (no hypotheses exist at this level)
                try self.dischargeTccs(null, @enumFromInt(0), 0);
                // registered unproven first: a self-citation is then caught by
                // the kernel as "cites unproven theorem"
                _ = try self.env.addStatement(self.file, name, .{ .theorem = .{
                    .name = name,
                    .formula = typed.id,
                    .loc = d.name.start,
                    .proven = false,
                } });
                if (self.trusted) {
                    // imported without --recursive: the proof is NOT checked
                    const fact = &self.env.findStatement(self.file, name).?.theorem;
                    fact.proven = true;
                    fact.trusted = true;
                } else {
                    self.accelerated_used.clearRetainingCapacity();
                    self.holes_used.clearRetainingCapacity();
                    const proven = try self.checkProofSteps(d.steps, typed.id, d.name.start);
                    if (proven) {
                        const fact = &self.env.findStatement(self.file, name).?.theorem;
                        fact.proven = true;
                        fact.accelerated = try self.arena.dupe(StrId, self.accelerated_used.items);
                        fact.holes = try self.arena.dupe(StrId, self.holes_used.items);
                    }
                }
            },
            .model => |d| try self.elaborateModel(d),
        }
    }

    /// Resolve a `model <Name> = <carrier> [where <guard>] { src: tgt ... }`
    /// declaration into a stored `Model` (an interpretation), keyed by name.
    /// Each mapping's source (a qualified theory entity) and target (a local
    /// entity) are resolved to ids; sorts feed the sort-map, funcs/consts/preds
    /// the sym-map. Axiom mappings are recorded but NOT checked here (the MVP
    /// `--fast` transfer trusts them; strict-mode obligation discharge is a
    /// later stage). See MODEL-DESIGN.md.
    fn elaborateModel(self: *Elaborator, d: anytype) ElabError!void {
        const name = try self.internTok(d.name);
        try self.checkFreshName(name, d.name);

        // carrier: a local sort.
        const carrier = self.env.findSort(self.file, try self.internTok(d.carrier)) orelse
            return self.fail(d.carrier.start, "model carrier '{s}' is not a sort in scope", .{self.text(d.carrier)});

        // optional guard: a local UNARY predicate over the carrier.
        var guard: ?term.Pool.Remap.Guard = null;
        if (d.guard) |g| {
            const gsym_id = self.env.findSym(self.file, try self.internTok(g)) orelse
                return self.fail(g.start, "model guard '{s}' is not a predicate in scope", .{self.text(g)});
            const gsym = self.env.sym(gsym_id);
            if (gsym.kind != .pred or gsym.arg_sorts.len != 1 or gsym.arg_sorts[0] != carrier) {
                return self.fail(g.start, "model guard '{s}' must be a unary predicate over the carrier sort", .{self.text(g)});
            }
            guard = .{ .pred = gsym_id, .carrier = carrier };
        }

        var sort_map: std.ArrayList(term.Pool.Remap.SortPair) = .empty;
        var sym_map: std.ArrayList(term.Pool.Remap.SymPair) = .empty;
        var source_file: ?FileId = null;

        for (d.mappings) |m| {
            const src = try self.resolveTarget(m.source);
            const tgt = try self.resolveTarget(m.target);
            // every source must be qualified (name a theory); record its file so
            // cited source theorems resolve at their origin.
            if (src.file == self.file) {
                return self.fail(m.source.start, "model mapping source '{s}' must name the abstract theory (e.g. group.op)", .{self.text(m.source)});
            }
            if (source_file) |sf| {
                if (sf != src.file) return self.fail(m.source.start, "all model mappings must come from one source theory", .{});
            } else source_file = src.file;

            // dispatch on what the source entity is: sort, symbol, or statement.
            if (self.env.findSort(src.file, src.base)) |from_sort| {
                const to_sort = self.env.findSort(tgt.file, tgt.base) orelse
                    return self.fail(m.target.start, "'{s}' is not a sort", .{self.text(m.target)});
                try sort_map.append(self.arena, .{ .from = from_sort, .to = to_sort });
            } else if (self.env.findSym(src.file, src.base)) |from_sym| {
                const to_sym = self.env.findSym(tgt.file, tgt.base) orelse
                    return self.fail(m.target.start, "'{s}' is not a function/predicate", .{self.text(m.target)});
                try sym_map.append(self.arena, .{ .from = from_sym, .to = to_sym });
            } else if (self.env.findStatementId(src.file, src.base)) |_| {
                // axiom obligation: recorded structurally by the source theorem
                // transfer at cite time; the target fact discharges it. The MVP
                // --fast path does not check the discharge here.
            } else {
                return self.fail(m.source.start, "unknown model mapping source '{s}'", .{self.text(m.source)});
            }
        }

        const remap: term.Pool.Remap = .{
            .sorts = try sort_map.toOwnedSlice(self.arena),
            .syms = try sym_map.toOwnedSlice(self.arena),
            .guard = guard,
        };
        try self.models.put(self.arena, name, .{
            .remap = remap,
            .source_file = source_file orelse self.file,
            .loc = d.name.start,
        });
    }

    // --- proof lowering: surface Fitch tree -> kernel steps + blocks ---

    const Lowering = struct {
        steps: std.ArrayList(kernel.Step) = .empty,
        blocks: std.ArrayList(kernel.Block) = .empty,
        labels: std.AutoHashMapUnmanaged(StrId, LabelTarget) = .empty,

        const LabelTarget = union(enum) { step: kernel.StepId, block: kernel.BlockId };
    };

    /// Lower and kernel-check a proof. Returns true if proven. Lowering
    /// errors record a diagnostic and yield false (the file continues).
    fn checkProofSteps(self: *Elaborator, steps: []const ast.Step, goal: TermId, goal_loc: u32) Allocator.Error!bool {
        var low: Lowering = .{};
        const root_label = try self.interner.intern("proof");
        try low.blocks.append(self.arena, .{
            .parent = null,
            .label = root_label,
            .kind = .root,
            .first_step = 0,
            .last_step = 0,
        });
        self.lowerSteps(&low, steps, @enumFromInt(0)) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return false,
        };
        low.blocks.items[0].last_step = @intCast(low.steps.items.len);

        var k: kernel.Kernel = .{
            .arena = self.arena,
            .pool = self.pool,
            .env = self.env,
            .interner = self.interner,
            .sink = self.sink,
        };
        return k.check(
            .{ .steps = low.steps.items, .blocks = low.blocks.items },
            goal,
            goal_loc,
        );
    }

    /// Lower a block's sibling steps. Labels resolve across the whole block
    /// regardless of textual order: the steps are topologically sorted by
    /// their intra-block citations before lowering, so a step may cite a
    /// later-written label. The kernel still receives strictly-backward
    /// references (dependencies lower first); a citation cycle is a located
    /// error. Ties break by textual order, so already-ordered proofs lower
    /// identically to before.
    fn lowerSteps(self: *Elaborator, low: *Lowering, steps: []const ast.Step, block_id: kernel.BlockId) ElabError!void {
        // map each sibling label to its textual index, catching duplicates
        // within this block and shadowing of an enclosing-scope label (Zig's
        // no-shadowing rule; disjoint sibling blocks may still reuse a name).
        var index_of: std.AutoHashMapUnmanaged(StrId, usize) = .empty;
        for (steps, 0..) |*s, i| {
            const label = try self.internTok(s.label);
            if (self.labelInScope(low, label, block_id)) {
                return self.fail(s.label.start, "label '{s}' shadows an enclosing label; choose a fresh name", .{self.text(s.label)});
            }
            const gop = index_of.getOrPut(self.arena, label) catch return error.OutOfMemory;
            if (gop.found_existing) {
                return self.fail(s.label.start, "duplicate label '{s}'", .{self.text(s.label)});
            }
            gop.value_ptr.* = i;
        }
        const order = try self.topoSortSteps(steps, index_of);
        for (order) |i| {
            try self.lowerOneStep(low, &steps[i], block_id);
        }
    }

    /// Is `label` already defined in `block_id` or an enclosing (ancestor)
    /// block — i.e. would (re)defining it here be *shadowing*? A label defined
    /// in a disjoint, already-closed sibling block is NOT in scope (reuse is
    /// fine); only the ancestor chain counts. Labels linger in `low.labels`
    /// after their block closes (parent discharge rules still cite into closed
    /// subproofs), so scope is decided structurally, by walking parents.
    fn labelInScope(self: *Elaborator, low: *const Lowering, label: StrId, block_id: kernel.BlockId) bool {
        _ = self;
        const target = low.labels.get(label) orelse return false;
        // the block the label lives *in*: a step's own block; a sub-block label
        // is registered in its parent's scope, so its home is that parent.
        const home: ?kernel.BlockId = switch (target) {
            .step => |id| low.steps.items[@intFromEnum(id)].block,
            .block => |id| low.blocks.items[@intFromEnum(id)].parent,
        };
        var cur: ?kernel.BlockId = block_id;
        while (cur) |c| {
            if (home == c) return true;
            cur = low.blocks.items[@intFromEnum(c)].parent;
        }
        return false;
    }

    /// Citations a step makes to labels *in its own block* (intra-block
    /// dependency edges). Enclosing-block labels and statement names are not
    /// edges — they are already available.
    fn stepSiblingDeps(step: *const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize), interner: *intern.Interner, source: []const u8, out: *std.ArrayList(usize), arena: Allocator) !void {
        const tok = struct {
            fn ref(t: lexer.Token, idx: std.AutoHashMapUnmanaged(StrId, usize), in: *intern.Interner, src: []const u8, o: *std.ArrayList(usize), a: Allocator) !void {
                const name = in.intern(src[t.start..t.end]) catch return error.OutOfMemory;
                if (idx.get(name)) |dep| try o.append(a, dep);
            }
        };
        switch (step.body) {
            .claim => |c| for (c.refs) |r| try tok.ref(r, index_of, interner, source, out, arena),
            .unpack => |blk| try tok.ref(blk.from, index_of, interner, source, out, arena),
            .case => |c| try tok.ref(c.disj, index_of, interner, source, out, arena),
            .assume, .fix => {}, // no header citations
        }
    }

    /// Topologically sort the sibling steps so every intra-block citation
    /// points to an earlier position. Kahn's algorithm; ties (independent
    /// steps) resolve in textual order for stable, unchanged output. A cycle
    /// is reported by name.
    fn topoSortSteps(self: *Elaborator, steps: []const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize)) ElabError![]const usize {
        const n = steps.len;
        // deps[i] = the sibling indices step i cites; dependents count for Kahn
        const deps = try self.arena.alloc([]const usize, n);
        const remaining = try self.arena.alloc(usize, n); // unlowered deps of i
        for (steps, 0..) |*s, i| {
            var d: std.ArrayList(usize) = .empty;
            try stepSiblingDeps(s, index_of, self.interner, self.source, &d, self.arena);
            deps[i] = d.items;
            remaining[i] = d.items.len;
        }
        var order: std.ArrayList(usize) = .empty;
        // repeatedly emit the lowest-index step whose deps are all emitted
        var emitted = try self.arena.alloc(bool, n);
        @memset(emitted, false);
        while (order.items.len < n) {
            var progressed = false;
            for (0..n) |i| {
                if (emitted[i] or remaining[i] != 0) continue;
                emitted[i] = true;
                try order.append(self.arena, i);
                // decrement dependents: any j citing i now has one fewer dep
                for (0..n) |j| {
                    if (emitted[j]) continue;
                    for (deps[j]) |dj| {
                        if (dj == i) remaining[j] -= 1;
                    }
                }
                progressed = true;
                break; // restart scan from lowest index for textual-order ties
            }
            if (!progressed) return self.reportCycle(steps, deps, emitted);
        }
        return order.items;
    }

    /// Emit a located "cyclic justification: a -> b -> ... -> a" error from
    /// the remaining unemitted steps (which form at least one cycle).
    fn reportCycle(self: *Elaborator, steps: []const ast.Step, deps: []const []const usize, emitted: []const bool) ElabError {
        // find a cycle by walking dependency edges among unemitted nodes
        var start: usize = 0;
        while (start < steps.len and emitted[start]) start += 1;
        var path: std.ArrayList(usize) = .empty;
        var on_path = self.arena.alloc(bool, steps.len) catch return error.OutOfMemory;
        @memset(on_path, false);
        var cur = start;
        while (!on_path[cur]) {
            on_path[cur] = true;
            path.append(self.arena, cur) catch return error.OutOfMemory;
            // step into the first unemitted dependency
            var next: ?usize = null;
            for (deps[cur]) |d| {
                if (!emitted[d]) {
                    next = d;
                    break;
                }
            }
            cur = next orelse break; // should not happen: a stuck node has a dep
        }
        // the cycle is path[first-occurrence-of-cur .. ] then cur again
        var msg: std.Io.Writer.Allocating = .init(self.arena);
        var started = false;
        for (path.items) |i| {
            if (!started and i != cur) continue;
            started = true;
            msg.writer.print("{s} -> ", .{self.text(steps[i].label)}) catch return error.OutOfMemory;
        }
        msg.writer.print("{s}", .{self.text(steps[cur].label)}) catch return error.OutOfMemory;
        return self.fail(steps[cur].label.start, "cyclic justification: {s}", .{msg.written()});
    }

    /// Lower one sibling step (claim or sub-block). Its label's real id is
    /// recorded here; because callers lower in topological order, any label
    /// this step cites is already resolved.
    fn lowerOneStep(self: *Elaborator, low: *Lowering, s: *const ast.Step, block_id: kernel.BlockId) ElabError!void {
        const label = try self.internTok(s.label);
        {
            switch (s.body) {
                .assume => |blk| {
                    const tcc_start = self.pending_tccs.items.len;
                    const f = try self.requireProp(try self.elaborateExpr(blk.formula), blk.formula);
                    // the assumption's guards are owed in the PARENT context
                    try self.dischargeTccs(low, block_id, tcc_start);
                    const b = try self.newBlock(low, label, block_id, .{ .assume = f.id });
                    low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
                    try self.lowerSteps(low, blk.steps, b);
                    self.closeBlock(low, b);
                },
                .fix => |blk| {
                    const v = try self.bindProofVar(blk.name, blk.sort);
                    const b = try self.newBlock(low, label, block_id, .{ .fix = v });
                    low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
                    try self.lowerSteps(low, blk.steps, b);
                    self.closeBlock(low, b);
                    _ = self.scope.pop();
                },
                .unpack => |blk| {
                    const source = try self.resolveStepRef(low, blk.from);
                    const v = try self.bindProofVar(blk.name, blk.sort);
                    const b = try self.newBlock(low, label, block_id, .{ .unpack = .{ .v = v, .source = source } });
                    low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
                    try self.lowerSteps(low, blk.steps, b);
                    self.closeBlock(low, b);
                    _ = self.scope.pop();
                },
                .claim => |c| {
                    const tcc_start = self.pending_tccs.items.len;
                    const f = try self.requireProp(try self.elaborateExpr(c.formula), c.formula);
                    const just = try self.lowerJustification(low, block_id, f.id, c);
                    // guards owed by the claim (and by rule arguments/schema
                    // instances) are discharged in this step's context
                    try self.dischargeTccs(low, block_id, tcc_start);
                    low.labels.put(self.arena, label, .{ .step = @enumFromInt(low.steps.items.len) }) catch return error.OutOfMemory;
                    try low.steps.append(self.arena, .{
                        .formula = f.id,
                        .just = just,
                        .block = block_id,
                        .label = label,
                        .loc = s.label.start,
                    });
                },
                .case => |c| try self.lowerCase(low, s, block_id, label, c),
            }
        }
    }

    /// Lower a `case` step: eliminate the cited disjunction (optionally after
    /// unpacking an existential witness) by fanning out the user's arms into a
    /// nested `or_elim` tree. The step's own claim is the shared goal; every
    /// arm must conclude it. The kernel checks the synthesized or_elim tree
    /// exactly as if hand-written, so this adds no trust.
    fn lowerCase(self: *Elaborator, low: *Lowering, s: *const ast.Step, block_id: kernel.BlockId, label: StrId, c: ast.Step.CaseBlock) ElabError!void {
        const loc = s.label.start;
        const goal_tcc = self.pending_tccs.items.len;
        // the case step advances a goal, stated on the step line like a claim
        const goal = try self.requireProp(try self.elaborateExpr(c.goal), c.goal);
        try self.dischargeTccs(low, block_id, goal_tcc);
        // the goal is a normal step in this block, justified by the (possibly
        // nested) or_elim tree fanned out over the cited disjunction's arms.
        const disj = try self.resolveStepRef(low, c.disj);
        const just = try self.emitCaseTree(low, block_id, loc, disj, c.arms, goal.id);
        low.labels.put(self.arena, label, .{ .step = @enumFromInt(low.steps.items.len) }) catch return error.OutOfMemory;
        try low.steps.append(self.arena, .{ .formula = goal.id, .just = just, .block = block_id, .label = label, .loc = loc });
    }

    /// Lower one `case` arm as a fresh `assume <disjunct>` block whose steps are
    /// the arm's body; returns the block. The block's conclusion is checked by
    /// the kernel to match the arm's disjunct and the shared goal.
    fn emitArmBlock(self: *Elaborator, low: *Lowering, parent: kernel.BlockId, arm: ast.Step.CaseBlock.Arm, expected: TermId) ElabError!kernel.BlockId {
        const f = try self.requireProp(try self.elaborateExpr(arm.assumption), arm.assumption);
        if (!self.pool.alphaEq(f.id, expected)) {
            return self.fail(exprLoc(arm.assumption), "case arm assumes '{s}', but the disjunct here is '{s}'", .{
                try self.renderTerm(f.id), try self.renderTerm(expected),
            });
        }
        const b = try self.newBlock(low, try self.internTok(arm.label), parent, .{ .assume = f.id });
        low.labels.put(self.arena, try self.internTok(arm.label), .{ .block = b }) catch return error.OutOfMemory;
        try self.lowerSteps(low, arm.steps, b);
        self.closeBlock(low, b);
        return b;
    }

    /// Fan the arms out over the (left-nested) disjunction `disj_formula`,
    /// proved by step `disj`, into a nested `or_elim` tree concluding `goal`.
    /// Returns the justification proving `goal` in `parent`.
    fn emitCaseTree(self: *Elaborator, low: *Lowering, parent: kernel.BlockId, loc: u32, disj: kernel.SRef, arms: []const ast.Step.CaseBlock.Arm, goal: TermId) ElabError!kernel.Justification {
        const disj_formula = low.steps.items[@intFromEnum(disj.id)].formula;
        const node = self.pool.get(disj_formula);
        if (node != .bin or node.bin.op != .or_op) {
            return self.fail(loc, "case: 'on' step is '{s}', not a disjunction", .{try self.renderTerm(disj_formula)});
        }
        if (arms.len < 2) {
            return self.fail(loc, "case over a disjunction needs at least two arms", .{});
        }
        // right arm (last) matches the rhs disjunct; the lhs holds the rest.
        const right_block = try self.emitArmBlock(low, parent, arms[arms.len - 1], node.bin.rhs);
        const left_block = if (arms.len == 2)
            try self.emitArmBlock(low, parent, arms[0], node.bin.lhs)
        else blk: {
            // lhs is itself `L or R`: an assume block that re-splits it.
            const lb = try self.newBlock(low, try self.freshNamed("case"), parent, .{ .assume = node.bin.lhs });
            const hyp = try self.emitStep(low, lb, loc, node.bin.lhs, .{ .hypothesis = .{ .id = lb, .loc = loc } });
            const inner = try self.emitCaseTree(low, lb, loc, hyp, arms[0 .. arms.len - 1], goal);
            _ = try self.emitStep(low, lb, loc, goal, inner);
            self.closeBlock(low, lb);
            break :blk lb;
        };
        return .{ .or_elim = .{
            .disj = disj,
            .left = .{ .id = left_block, .loc = loc },
            .right = .{ .id = right_block, .loc = loc },
        } };
    }

    fn newBlock(self: *Elaborator, low: *Lowering, label: StrId, parent: kernel.BlockId, kind: kernel.Block.Kind) ElabError!kernel.BlockId {
        const id: kernel.BlockId = @enumFromInt(low.blocks.items.len);
        try low.blocks.append(self.arena, .{
            .parent = parent,
            .label = label,
            .kind = kind,
            .first_step = @intCast(low.steps.items.len),
            .last_step = 0,
        });
        return id;
    }

    fn closeBlock(self: *Elaborator, low: *Lowering, id: kernel.BlockId) void {
        _ = self;
        low.blocks.items[@intFromEnum(id)].last_step = @intCast(low.steps.items.len);
    }

    /// fix/unpack variable. Zig's rule: no *shadowing* — the name must be fresh
    /// against every enclosing-scope variable and every declaration, but a
    /// disjoint sibling subproof MAY reuse it.
    ///
    /// The kernel identifies an eigenvariable by its interned name, so two
    /// disjoint `fix x` blocks that both used the bare name `x` would produce
    /// representationally identical eigenvariables — and closing the second with
    /// `forall_intro` would trip `checkEigen` on the first block's (closed)
    /// `x`-steps, which the kernel cannot tell apart. To keep sibling reuse
    /// sound AND accepted, we bind the fix var to a FRESH disambiguated identity
    /// `x#<n>` in kernel terms while keeping the source name `x` for scope
    /// lookups and shadow-checks. `#` is not a legal identifier character, so
    /// the disambiguated name can never collide with a userland name, and the
    /// printer trims each fvar at `#` so proofs still render `x` (see
    /// `print.zig` `displayName`).
    fn bindProofVar(self: *Elaborator, name_tok: lexer.Token, sort_tok: lexer.Token) ElabError!term.Node.Fvar {
        const name = try self.internTok(name_tok);
        for (self.scope.items) |entry| {
            if (entry.name == name) {
                return self.fail(name_tok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(name_tok)});
            }
        }
        if (self.env.findSym(self.file, name) != null) {
            return self.fail(name_tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(name_tok)});
        }
        const sort = try self.resolveSort(sort_tok);
        const fvar = try self.freshNamed(self.text(name_tok));
        try self.scope.append(self.arena, .{ .name = name, .sort = sort, .fvar = fvar });
        return .{ .name = fvar, .sort = sort };
    }

    fn resolveStepRef(self: *Elaborator, low: *Lowering, tok: lexer.Token) ElabError!kernel.SRef {
        const name = try self.internTok(tok);
        const target = low.labels.get(name) orelse {
            // A common mistake is naming an axiom/theorem/schema where a proof
            // STEP is required (e.g. `forall_elim(a) unionMember` instead of
            // materializing `@ax | ... [by axiom unionMember]` first, then
            // `forall_elim(a) ax`). Detect that and point at the fix rather than
            // reporting a bare "unknown reference".
            const name_text = self.text(tok);
            if (self.statementByName(name)) |stmt| {
                // article + the intro keyword that materializes this kind as a step
                const desc: []const u8, const intro: []const u8 = switch (stmt) {
                    .axiom => .{ "an axiom", "axiom" },
                    .theorem => .{ "a theorem", "theorem" },
                    .schema => .{ "a schema", "instantiate" },
                };
                return self.fail(tok.start, "'{s}' is {s}, not a proof step; introduce it as a step first with `[by {s} {s}]`, then reference that step", .{
                    name_text, desc, intro, name_text,
                });
            }
            return self.fail(tok.start, "unknown reference '{s}'", .{name_text});
        };
        return switch (target) {
            .step => |id| .{ .id = id, .loc = tok.start },
            .block => self.fail(tok.start, "'{s}' names a subproof; a step reference is required", .{self.text(tok)}),
        };
    }

    /// Look up a statement (axiom/theorem/schema) visible by name in the theory
    /// scope or the current file — used to sharpen "unknown reference" hints.
    fn statementByName(self: *Elaborator, name: StrId) ?Statement {
        const id = self.env.findStatementId(self.theoryScope(), name) orelse
            self.env.findStatementId(self.file, name) orelse return null;
        return self.env.statements.items[@intFromEnum(id)];
    }

    fn resolveBlockRef(self: *Elaborator, low: *Lowering, tok: lexer.Token) ElabError!kernel.BRef {
        const name = try self.internTok(tok);
        const target = low.labels.get(name) orelse {
            return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)});
        };
        return switch (target) {
            .block => |id| .{ .id = id, .loc = tok.start },
            .step => self.fail(tok.start, "'{s}' names a step; a subproof reference is required", .{self.text(tok)}),
        };
    }

    fn resolveStatementRef(self: *Elaborator, tok: lexer.Token) ElabError!StatementId {
        const target = try self.resolveTarget(tok);
        return self.env.findStatementId(target.file, target.base) orelse
            self.fail(tok.start, "unknown statement '{s}'", .{self.text(tok)});
    }

    const RuleKind = enum {
        axiom,
        theorem,
        hypothesis,
        modus_ponens,
        implies_intro,
        forall_intro,
        forall_elim,
        exists_intro,
        exists_elim,
        and_intro,
        and_elim_left,
        and_elim_right,
        or_intro_left,
        or_intro_right,
        or_elim,
        not_intro,
        absurd,
        double_negation,
        reflexivity,
        symmetry,
        rewrite,
        instantiate,
        simplify,
        simplify_quantified,
        ac,
        ac_quantified,
        assoc,
        assoc_quantified,
        polynomial,
        polynomial_quantified,
        tautology,
        arithmetic,
        ext,
        ext_quantified,
        model,
    };

    const rule_names = std.StaticStringMap(RuleKind).initComptime(.{
        .{ "axiom", .axiom },
        .{ "theorem", .theorem },
        .{ "hypothesis", .hypothesis },
        .{ "modus_ponens", .modus_ponens },
        .{ "implies_intro", .implies_intro },
        .{ "forall_intro", .forall_intro },
        .{ "forall_elim", .forall_elim },
        .{ "exists_intro", .exists_intro },
        .{ "exists_elim", .exists_elim },
        .{ "and_intro", .and_intro },
        .{ "and_elim_left", .and_elim_left },
        .{ "and_elim_right", .and_elim_right },
        .{ "or_intro_left", .or_intro_left },
        .{ "or_intro_right", .or_intro_right },
        .{ "or_elim", .or_elim },
        .{ "not_intro", .not_intro },
        .{ "absurd", .absurd },
        .{ "double_negation", .double_negation },
        .{ "symmetry", .symmetry },
        .{ "reflexivity", .reflexivity },
        .{ "rewrite", .rewrite },
        .{ "instantiate", .instantiate },
        .{ "simplify", .simplify },
        .{ "simplify_quantified", .simplify_quantified },
        .{ "assoc_commut", .ac },
        .{ "assoc_commut_quantified", .ac_quantified },
        .{ "assoc", .assoc },
        .{ "assoc_quantified", .assoc_quantified },
        .{ "polynomial", .polynomial },
        .{ "polynomial_quantified", .polynomial_quantified },
        .{ "tautology", .tautology },
        .{ "arithmetic", .arithmetic },
        .{ "ext", .ext },
        .{ "ext_quantified", .ext_quantified },
        .{ "model", .model },
    });

    fn lowerJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const kind = rule_names.get(self.text(c.rule)) orelse {
            return self.fail(c.rule.start, "unknown rule '{s}'", .{self.text(c.rule)});
        };
        // argument-count discipline
        const wants_args: usize = switch (kind) {
            // forall_elim specializes at one OR MORE arguments (a multi-arg
            // call emits the intermediate chain); zero arguments is an error.
            .forall_elim => if (c.args.len == 0) 1 else c.args.len,
            .exists_intro => 1,
            .instantiate => c.args.len, // schema-dependent, checked in M4
            // assoc_commut takes an OPTIONAL explicit AC triple
            // `(assoc, comm, swap)` for a custom operator; bare = well-known
            // add/mul. Exactly-0-or-3 is validated inside the tactic.
            .ac, .ac_quantified => c.args.len,
            // assoc REQUIRES exactly one arg (the associativity lemma); the
            // "requires an associativity lemma" message is emitted in the
            // tactic so a bare `assoc` gets a helpful error, not a generic one.
            .assoc, .assoc_quantified => c.args.len,
            else => 0,
        };
        if (c.args.len != wants_args) {
            return self.fail(c.rule.start, "'{s}' expects {d} argument(s), got {d}", .{
                self.text(c.rule), wants_args, c.args.len,
            });
        }
        switch (kind) {
            .axiom => {
                try self.wantRefs(c, 1);
                const stmt_id = try self.resolveStatementRef(c.refs[0]);
                // a `hole` is stored as an axiom-kind Fact with is_hole set;
                // citing one makes the current theorem rest on that hole.
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                if (stmt == .axiom and stmt.axiom.is_hole) try self.inheritHoles(stmt.axiom.holes);
                return .{ .axiom_ref = .{ .stmt = stmt_id, .loc = c.refs[0].start } };
            },
            .theorem => {
                try self.wantRefs(c, 1);
                const stmt_id = try self.resolveStatementRef(c.refs[0]);
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                if (stmt == .theorem) {
                    try self.inheritAccelerated(stmt.theorem.accelerated);
                    try self.inheritHoles(stmt.theorem.holes);
                }
                return .{ .theorem_ref = .{ .stmt = stmt_id, .loc = c.refs[0].start } };
            },
            .hypothesis => {
                try self.wantRefs(c, 1);
                return .{ .hypothesis = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .modus_ponens => {
                try self.wantRefs(c, 2);
                return .{ .modus_ponens = .{
                    .implication = try self.resolveStepRef(low, c.refs[0]),
                    .antecedent = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .implies_intro => {
                try self.wantRefs(c, 1);
                return .{ .implies_intro = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .forall_intro => {
                try self.wantRefs(c, 1);
                return .{ .forall_intro = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .forall_elim => {
                try self.wantRefs(c, 1);
                // `forall_elim(A, B, C) ref` specializes at several arguments
                // in one written step: each argument but the last emits an
                // intermediate forall_elim step (kernel-checked as usual); the
                // last becomes this step's own justification.
                var cur = try self.resolveStepRef(low, c.refs[0]);
                var cur_formula = low.steps.items[@intFromEnum(cur.id)].formula;
                for (c.args[0 .. c.args.len - 1]) |arg_expr| {
                    const node = self.pool.get(cur_formula);
                    if (node != .quant or node.quant.q != .forall) {
                        return self.fail(exprLoc(arg_expr), "forall_elim: '{s}' is not universally quantified here", .{try self.renderTerm(cur_formula)});
                    }
                    const arg = try self.elaborateExpr(arg_expr);
                    const opened = try self.pool.open(node.quant.body, arg.id);
                    cur = try self.emitStep(low, block_id, exprLoc(arg_expr), opened, .{
                        .forall_elim = .{ .step = cur, .with = arg.id, .with_loc = exprLoc(arg_expr) },
                    });
                    cur_formula = opened;
                }
                const last = c.args[c.args.len - 1];
                const arg = try self.elaborateExpr(last);
                return .{ .forall_elim = .{
                    .step = cur,
                    .with = arg.id,
                    .with_loc = exprLoc(last),
                } };
            },
            .exists_intro => {
                try self.wantRefs(c, 1);
                const arg = try self.elaborateExpr(c.args[0]);
                return .{ .exists_intro = .{
                    .step = try self.resolveStepRef(low, c.refs[0]),
                    .witness = arg.id,
                    .witness_loc = exprLoc(c.args[0]),
                } };
            },
            .exists_elim => {
                try self.wantRefs(c, 1);
                return .{ .exists_elim = try self.resolveBlockRef(low, c.refs[0]) };
            },
            .and_intro => {
                try self.wantRefs(c, 2);
                return .{ .and_intro = .{
                    .left = try self.resolveStepRef(low, c.refs[0]),
                    .right = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .and_elim_left => {
                try self.wantRefs(c, 1);
                return .{ .and_elim_left = try self.resolveStepRef(low, c.refs[0]) };
            },
            .and_elim_right => {
                try self.wantRefs(c, 1);
                return .{ .and_elim_right = try self.resolveStepRef(low, c.refs[0]) };
            },
            .or_intro_left => {
                try self.wantRefs(c, 1);
                return .{ .or_intro_left = try self.resolveStepRef(low, c.refs[0]) };
            },
            .or_intro_right => {
                try self.wantRefs(c, 1);
                return .{ .or_intro_right = try self.resolveStepRef(low, c.refs[0]) };
            },
            .or_elim => {
                try self.wantRefs(c, 3);
                return .{ .or_elim = .{
                    .disj = try self.resolveStepRef(low, c.refs[0]),
                    .left = try self.resolveBlockRef(low, c.refs[1]),
                    .right = try self.resolveBlockRef(low, c.refs[2]),
                } };
            },
            .not_intro => {
                try self.wantRefs(c, 3);
                return .{ .not_intro = .{
                    .block = try self.resolveBlockRef(low, c.refs[0]),
                    .s1 = try self.resolveStepRef(low, c.refs[1]),
                    .s2 = try self.resolveStepRef(low, c.refs[2]),
                } };
            },
            .absurd => {
                try self.wantRefs(c, 2);
                return .{ .absurd = .{
                    .s1 = try self.resolveStepRef(low, c.refs[0]),
                    .s2 = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .double_negation => {
                try self.wantRefs(c, 1);
                return .{ .double_negation = try self.resolveStepRef(low, c.refs[0]) };
            },
            .reflexivity => {
                try self.wantRefs(c, 0);
                return .reflexivity;
            },
            .symmetry => {
                try self.wantRefs(c, 1);
                return .{ .symmetry = try self.resolveStepRef(low, c.refs[0]) };
            },
            .rewrite => {
                try self.wantRefs(c, 2);
                return .{ .rewrite = .{
                    .equation = try self.resolveStepRef(low, c.refs[0]),
                    .target = try self.resolveStepRef(low, c.refs[1]),
                } };
            },
            .simplify => {
                return self.simplifyJustification(low, block_id, goal, c);
            },
            .simplify_quantified => {
                return self.simplifyQuantifiedJustification(low, block_id, goal, c);
            },
            .ac => {
                return self.acJustification(low, block_id, goal, c);
            },
            .ac_quantified => {
                return self.acQuantifiedJustification(low, block_id, goal, c);
            },
            .assoc => {
                return self.assocJustification(low, block_id, goal, c);
            },
            .assoc_quantified => {
                return self.assocQuantifiedJustification(low, block_id, goal, c);
            },
            .polynomial => {
                return self.polynomialJustification(low, block_id, goal, c);
            },
            .polynomial_quantified => {
                return self.polynomialQuantifiedJustification(low, block_id, goal, c);
            },
            .tautology => {
                return self.tautologyJustification(low, block_id, goal, c);
            },
            .arithmetic => {
                return self.arithmeticJustification(low, block_id, goal, c);
            },
            .ext => {
                return self.extJustification(low, block_id, goal, c, false);
            },
            .ext_quantified => {
                return self.extJustification(low, block_id, goal, c, true);
            },
            .model => {
                return self.modelJustification(goal, c);
            },
            .instantiate => {
                const name_tok = c.schema.?; // parser guarantees presence
                const stmt_id = try self.resolveStatementRef(name_tok);
                const stmt = &self.env.statements.items[@intFromEnum(stmt_id)];
                if (stmt.* != .schema) {
                    return self.fail(name_tok.start, "'{s}' is not a schema", .{self.text(name_tok)});
                }
                const inst = try self.instantiateSchema(stmt_id, &stmt.schema, c);
                const premises = try self.arena.alloc(kernel.SRef, c.refs.len);
                for (c.refs, premises) |r, *out| out.* = try self.resolveStepRef(low, r);
                return .{ .schema_instance = .{ .instance = inst, .premises = premises } };
            },
        }
    }

    /// Check obligations [start..] against what is available, then drop them.
    /// ALL undischarged obligations are reported (not just the first), each
    /// with its exact formula in copy-pasteable surface syntax.
    fn dischargeTccs(self: *Elaborator, low: ?*const Lowering, block_id: kernel.BlockId, start: usize) ElabError!void {
        if (self.trusted) {
            self.pending_tccs.shrinkRetainingCapacity(start);
            return;
        }
        var any_failed = false;
        for (self.pending_tccs.items[start..]) |t| {
            if (!try self.tccDischarged(low, block_id, t.formula)) {
                const rendered = @import("print.zig").render(self.arena, self.pool, self.env, self.interner, t.formula) catch return error.OutOfMemory;
                self.sink.add(t.loc, "unproved obligation: '{s}'", .{rendered}) catch return error.OutOfMemory;
                any_failed = true;
            }
        }
        self.pending_tccs.shrinkRetainingCapacity(start);
        if (any_failed) return error.Recover;
    }

    /// An obligation is discharged by an EXACT (alpha-equal) match against an
    /// axiom, a proven theorem, an in-scope hypothesis, or an accessible step
    /// — NO proof search. Before matching, the obligation is decomposed
    /// structurally (deterministic, linear): `forall x. B` introduces a fresh
    /// eigenvariable, `A -> B` moves A into local hypotheses. This makes
    /// tautological wrappers (`d != ZERO -> d != ZERO`) self-discharging while
    /// anything substantive still requires an explicit lemma or step.
    fn tccDischarged(self: *Elaborator, low: ?*const Lowering, block_id: kernel.BlockId, formula: TermId) ElabError!bool {
        var hyps: std.ArrayList(TermId) = .empty;
        var f = formula;
        while (true) {
            for (hyps.items) |h| {
                if (self.pool.alphaEq(h, f)) return true;
            }
            if (self.tccMatches(low, block_id, f)) return true;
            const node = self.pool.get(f);
            if (node == .bin and node.bin.op == .implies) {
                try hyps.append(self.arena, node.bin.lhs);
                f = node.bin.rhs;
                continue;
            }
            if (node == .quant and node.quant.q == .forall) {
                const fresh = try self.freshName();
                const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
                f = try self.pool.open(node.quant.body, fv);
                continue;
            }
            return false;
        }
    }

    fn tccMatches(self: *Elaborator, low: ?*const Lowering, block_id: kernel.BlockId, f: TermId) bool {
        for (self.env.statements.items) |stmt| {
            const known: TermId = switch (stmt) {
                .axiom => |a| a.formula,
                .theorem => |t| if (t.proven) t.formula else continue,
                .schema => continue,
            };
            if (self.pool.alphaEq(known, f)) return true;
        }
        const l = low orelse return false;
        // hypotheses on the ancestor chain
        var cur: ?kernel.BlockId = block_id;
        while (cur) |c| {
            const b = l.blocks.items[@intFromEnum(c)];
            if (b.kind == .assume and self.pool.alphaEq(b.kind.assume, f)) return true;
            cur = b.parent;
        }
        // accessible prior steps
        for (l.steps.items) |s| {
            if (!lowAncestorOrSelf(l, s.block, block_id)) continue;
            if (self.pool.alphaEq(s.formula, f)) return true;
        }
        return false;
    }

    fn lowAncestorOrSelf(low: *const Lowering, a: kernel.BlockId, b: kernel.BlockId) bool {
        var cur: ?kernel.BlockId = b;
        while (cur) |c| {
            if (c == a) return true;
            cur = low.blocks.items[@intFromEnum(c)].parent;
        }
        return false;
    }

    /// Monomorphize a schema at concrete, written-down arguments (comptime
    /// semantics). Value params substitute a term; generator params
    /// beta-reduce a single-argument lambda at the term level (capture-proof:
    /// all terms involved are locally closed). A proof-carrying schema has its
    /// proof re-elaborated and kernel-checked at THIS instance.
    fn statementName(stmt: Statement) StrId {
        return switch (stmt) {
            .axiom => |f| f.name,
            .theorem => |f| f.name,
            .schema => |s| s.name,
        };
    }

    fn instantiateSchema(self: *Elaborator, stmt_id: StatementId, schema: *const Statement.Schema, c: ast.Step.Claim) ElabError!TermId {
        const name_tok = c.schema.?;
        // cycle detection: a schema that appears in its own instantiation
        // chain would re-check its proof forever. Report the chain by name.
        for (self.instantiating.items, 0..) |on_stack, i| {
            if (on_stack == stmt_id) {
                var msg: std.Io.Writer.Allocating = .init(self.arena);
                for (self.instantiating.items[i..]) |sid| {
                    const s = self.env.statements.items[@intFromEnum(sid)];
                    msg.writer.print("{s} -> ", .{self.interner.str(statementName(s))}) catch return error.OutOfMemory;
                }
                msg.writer.print("{s}", .{self.text(name_tok)}) catch return error.OutOfMemory;
                return self.fail(name_tok.start, "schema instantiation cycle: {s}", .{msg.written()});
            }
        }
        // a huge backstop purely to bound memory on a pathological (but
        // acyclic) blowup; far above any real proof
        if (self.instantiating.items.len >= 1024) {
            return self.fail(name_tok.start, "schema instantiation nested past 1024 (runaway?)", .{});
        }
        if (c.args.len != schema.params.len) {
            return self.fail(name_tok.start, "schema '{s}' expects {d} argument(s), got {d}", .{
                self.text(name_tok), schema.params.len, c.args.len,
            });
        }

        // the schema's SIGNATURE tokens (param names, param sorts) live in the
        // defining file; the ARGUMENT expressions live at the use site. Swap
        // contexts per operation.
        const schema_ctx: Ctx = .{
            .source = schema.source,
            .file = schema.file,
            .diag = @intFromEnum(schema.file),
        };
        var args_map: SchemaArgs = .empty;
        for (schema.params, c.args) |p, arg_expr| {
            const ctx = self.swapCtx(schema_ctx);
            const pname = try self.internTok(p.name);
            if (p.arg_sorts.len == 0) {
                const want = try self.resolveSort(p.result);
                _ = self.swapCtx(ctx);
                const t = try self.elaborateExpr(arg_expr);
                if (t.sort != want) {
                    return self.fail(exprLoc(arg_expr), "expected sort '{s}', got '{s}'", .{
                        self.sortName(want), self.sortName(t.sort),
                    });
                }
                args_map.put(self.arena, pname, .{ .value = t }) catch return error.OutOfMemory;
            } else {
                if (p.arg_sorts.len > 1) {
                    return self.fail(p.name.start, "schema parameters take at most one argument (for now)", .{});
                }
                const arg_sort = try self.resolveSort(p.arg_sorts[0]);
                const result_sort = try self.resolveSort(p.result);
                const pname_text = self.text(p.name);
                _ = self.swapCtx(ctx);
                // eta-sugar: a bare predicate name `p` (of the expected
                // `arg_sort -> result_sort` signature) stands for the lambda
                // `fun x => p(x)`. Synthesize that body directly at the term
                // level and store the same `.lambda` shape as the explicit form.
                if (arg_expr.* == .name and
                    std.mem.indexOfScalar(u8, self.text(arg_expr.name), '.') == null)
                {
                    const nm = try self.internTok(arg_expr.name);
                    if (self.env.findSym(self.file, nm)) |sym_id| {
                        const sym = self.env.sym(sym_id);
                        if (sym.kind == .pred and sym.arg_sorts.len == 1 and
                            sym.arg_sorts[0] == arg_sort and sym.result == result_sort)
                        {
                            const fresh = try self.freshName();
                            const fvar = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = arg_sort } });
                            const applied = try self.pool.addApp(.pred, sym_id, &.{fvar});
                            const closed = try self.pool.close(applied, fresh);
                            args_map.put(self.arena, pname, .{
                                .lambda = .{ .body = closed, .arg_sort = arg_sort, .result_sort = result_sort },
                            }) catch return error.OutOfMemory;
                            continue;
                        }
                    }
                }
                if (arg_expr.* != .lambda) {
                    return self.fail(exprLoc(arg_expr), "schema parameter '{s}' requires a lambda argument (or a bare predicate of sort '{s}' -> '{s}')", .{ pname_text, self.sortName(arg_sort), self.sortName(result_sort) });
                }
                const lam = arg_expr.lambda;
                if (lam.binders.len != 1) {
                    return self.fail(lam.tok.start, "schema parameter '{s}' expects a 1-argument lambda", .{pname_text});
                }
                const lam_sort = try self.resolveSort(lam.binders[0].sort);
                if (lam_sort != arg_sort) {
                    return self.fail(lam.binders[0].sort.start, "expected sort '{s}', got '{s}'", .{
                        self.sortName(arg_sort), self.sortName(lam_sort),
                    });
                }
                const lam_name = try self.internTok(lam.binders[0].name);
                try self.checkNoShadow(lam_name, lam.binders[0].name);
                const fresh = try self.freshName();
                try self.scope.append(self.arena, .{
                    .name = lam_name,
                    .sort = arg_sort,
                    .fvar = fresh,
                });
                const body = try self.elaborateExpr(lam.body);
                _ = self.scope.pop();
                if (body.sort != result_sort) {
                    if (result_sort == .prop) {
                        return self.fail(exprLoc(lam.body), "expected a proposition, got sort '{s}'", .{self.sortName(body.sort)});
                    }
                    return self.fail(exprLoc(lam.body), "expected sort '{s}', got '{s}'", .{
                        self.sortName(result_sort), self.sortName(body.sort),
                    });
                }
                const closed = try self.pool.close(body.id, fresh);
                args_map.put(self.arena, pname, .{
                    .lambda = .{ .body = closed, .arg_sort = arg_sort, .result_sort = result_sort },
                }) catch return error.OutOfMemory;
            }
        }

        return (try self.instantiateSchemaCore(stmt_id, schema, schema_ctx, &args_map)) orelse
            self.fail(name_tok.start, "instantiation of schema '{s}' failed here", .{self.text(name_tok)});
    }

    /// Monomorphize a schema's stored body/proof at a completed `args_map`
    /// (params -> value/lambda). Shared by the surface `instantiate` path
    /// (which builds args_map from written-down arguments) and synthesizing
    /// certifiers (which build a lambda arg directly from a TermId predicate —
    /// e.g. the Cooper-replay induction). Returns the monomorphized instance
    /// formula, or null on failure. The body/proof resolve in the schema's own
    /// defining file, hygienically masked from the use-site scope.
    fn instantiateSchemaCore(self: *Elaborator, stmt_id: StatementId, schema: *const Statement.Schema, schema_ctx: Ctx, args_map: *const SchemaArgs) ElabError!?TermId {
        const saved_scope = self.scope;
        const saved_args = self.schema_args;
        self.scope = .empty;
        self.schema_args = args_map;
        try self.instantiating.append(self.arena, stmt_id);
        defer {
            self.scope = saved_scope;
            self.schema_args = saved_args;
            _ = self.instantiating.pop();
        }

        const use_ctx = self.swapCtx(schema_ctx);
        const checked: ?TermId = blk: {
            const inst = self.requireProp(self.elaborateExpr(schema.body) catch |e| switch (e) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => break :blk null,
            }, schema.body) catch |e| switch (e) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => break :blk null,
            };
            // re-check the schema's proof at this instance (comptime-template
            // semantics). `--reckless` (recheck_schemas = false) trusts the
            // schema's stored proven-ness and skips the re-instantiation.
            if (self.verify.recheck_schemas) {
                if (schema.proof) |steps| {
                    if (!try self.checkProofSteps(steps, inst.id, schema.loc)) break :blk null;
                }
            }
            break :blk inst.id;
        };
        _ = self.swapCtx(use_ctx);
        return checked;
    }

    fn wantRefs(self: *Elaborator, c: ast.Step.Claim, n: usize) ElabError!void {
        if (c.refs.len != n) {
            return self.fail(c.rule.start, "'{s}' expects {d} reference(s), got {d}", .{
                self.text(c.rule), n, c.refs.len,
            });
        }
    }

    // --- the `simplify` tactic: certificate emitter -------------------------
    // Synthesizes ordinary kernel steps (reflexivity / axiom or theorem
    // citation / forall_elim specialization / rewrite) into the current block
    // and returns the user's claim justification. Every step kernel-checked: no
    // accelerated step, the kernel checks everything.

    // --- universal-prefix peeling (shared by arithmetic / simplify_quantified)

    /// A goal's `forall` prefix, stripped to its body. `opened[i]` is the
    /// goal after opening the first `i` binders (opened[0] = the whole goal,
    /// opened[len] = body); `fix_vars` are the fresh eigenvariables, one per
    /// peeled binder, outermost-first.
    const Universal = struct {
        opened: []const TermId,
        fix_vars: []const term.Node.Fvar,
        body: TermId,
    };

    /// Strip the outer `forall` binders of `goal`, opening each as a fresh
    /// eigenvariable named `prefix`.
    fn peelUniversal(self: *Elaborator, goal: TermId, prefix: []const u8) ElabError!Universal {
        var opened: std.ArrayList(TermId) = .empty;
        var fix_vars: std.ArrayList(term.Node.Fvar) = .empty;
        var g = goal;
        try opened.append(self.arena, g);
        while (true) {
            const node = self.pool.get(g);
            if (node != .quant or node.quant.q != .forall) break;
            const fv: term.Node.Fvar = .{ .name = try self.freshNamed(prefix), .sort = node.quant.sort };
            const fv_id = try self.pool.add(.{ .fvar = fv });
            g = try self.pool.open(node.quant.body, fv_id);
            try fix_vars.append(self.arena, fv);
            try opened.append(self.arena, g);
        }
        return .{ .opened = opened.items, .fix_vars = fix_vars.items, .body = g };
    }

    /// Open one synthesized `fix` block per peeled binder; returns the block
    /// ids (outermost-first) and the innermost block, which is where the body
    /// justification should be emitted. Pair with `closeUniversal`.
    fn openUniversal(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, u: Universal) ElabError!struct { blocks: []const kernel.BlockId, innermost: kernel.BlockId } {
        var blocks: std.ArrayList(kernel.BlockId) = .empty;
        var parent = block_id;
        for (u.fix_vars) |fv| {
            const b = try self.newBlock(low, try self.freshNamed("forall"), parent, .{ .fix = fv });
            try blocks.append(self.arena, b);
            parent = b;
        }
        return .{ .blocks = blocks.items, .innermost = parent };
    }

    /// Emit the body claim in the innermost block, then close each fix block
    /// with `forall_intro`, returning the outermost justification. When there
    /// are no binders, `body_just` is returned unchanged (nothing to close).
    fn closeUniversal(self: *Elaborator, low: *Lowering, loc: u32, u: Universal, blocks: []const kernel.BlockId, body_just: kernel.Justification) ElabError!kernel.Justification {
        if (blocks.len == 0) return body_just;
        _ = try self.emitStep(low, blocks[blocks.len - 1], loc, u.body, body_just);
        var i = blocks.len;
        while (i > 1) {
            i -= 1;
            self.closeBlock(low, blocks[i]);
            _ = try self.emitStep(low, blocks[i - 1], loc, u.opened[i], .{ .forall_intro = .{ .id = blocks[i], .loc = loc } });
        }
        self.closeBlock(low, blocks[0]);
        return .{ .forall_intro = .{ .id = blocks[0], .loc = loc } };
    }

    /// Append a synthesized step to the proof; returns a reference to it.
    fn emitStep(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, formula: TermId, just: kernel.Justification) ElabError!kernel.SRef {
        const id: kernel.StepId = @enumFromInt(low.steps.items.len);
        try low.steps.append(self.arena, .{
            .formula = formula,
            .just = just,
            .block = block_id,
            .label = try self.freshNamed("simplify"),
            .loc = loc,
        });
        return .{ .id = id, .loc = loc };
    }

    /// Emit the citation + forall_elim chain specializing `rule` at
    /// `bindings`; returns the step proving `inst_lhs = inst_rhs`.
    fn emitInstance(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, rule: simplify_mod.Rule, bindings: []const TermId) ElabError!kernel.SRef {
        var cur_ref: kernel.SRef = undefined;
        var cur_formula: TermId = rule.formula;
        switch (rule.source) {
            .axiom => |a| cur_ref = try self.emitStep(low, block_id, loc, rule.formula, .{ .axiom_ref = .{ .stmt = a.id, .loc = loc } }),
            .theorem => |t| cur_ref = try self.emitStep(low, block_id, loc, rule.formula, .{ .theorem_ref = .{ .stmt = t.id, .loc = loc } }),
            .step => |sref| cur_ref = sref, // already in the proof
        }
        for (bindings) |val| {
            const q = self.pool.get(cur_formula).quant;
            const opened = try self.pool.open(q.body, val);
            cur_ref = try self.emitStep(low, block_id, loc, opened, .{ .forall_elim = .{ .step = cur_ref, .with = val, .with_loc = loc } });
            cur_formula = opened;
        }
        return cur_ref;
    }

    /// Emit `eq(start, start)` then one rewrite step per trace entry;
    /// returns the step proving `eq(start, <after last entry>)`.
    /// `trace` must be non-empty.
    fn emitSideChain(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, rules: []const simplify_mod.Rule, start: TermId, trace: []const simplify_mod.Rewrite) ElabError!kernel.SRef {
        const refl = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = start } });
        var prev = try self.emitStep(low, block_id, loc, refl, .reflexivity);
        for (trace) |rw| {
            const inst = try self.emitInstance(low, block_id, loc, rules[rw.rule_idx], rw.bindings);
            const next = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = rw.after } });
            prev = try self.emitStep(low, block_id, loc, next, .{ .rewrite = .{ .equation = inst, .target = prev } });
        }
        return prev;
    }

    fn simplifyJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const goal_node = self.pool.get(goal);
        if (goal_node != .eq) {
            // a forall over an equation is the common mistake — point at the
            // tactic that handles it
            if (goal_node == .quant and goal_node.quant.q == .forall) {
                return self.fail(loc, "simplify proves equations; did you mean simplify_quantified?", .{});
            }
            return self.fail(loc, "simplify proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
        }
        return self.simplifyEquation(low, block_id, loc, c.refs, goal);
    }

    fn simplifyQuantifiedJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
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

    /// The simplify core on a bare equation goal `eq_goal` in `emit_block`:
    /// resolve cited refs into rules, normalize both sides, emit the join.
    fn simplifyEquation(self: *Elaborator, low: *Lowering, emit_block: kernel.BlockId, loc: u32, refs: []const lexer.Token, eq_goal: TermId) ElabError!kernel.Justification {
        const goal_node = self.pool.get(eq_goal);
        std.debug.assert(goal_node == .eq);

        // prepare rules from the cited facts (step labels first, then statements)
        var rules: std.ArrayList(simplify_mod.Rule) = .empty;
        for (refs) |ref| {
            const name = try self.internTok(ref);
            var formula: TermId = undefined;
            var source: simplify_mod.Source = undefined;
            if (low.labels.get(name)) |target| switch (target) {
                .step => |sid| {
                    const s = low.steps.items[@intFromEnum(sid)];
                    if (!lowAncestorOrSelf(low, s.block, emit_block)) {
                        return self.fail(ref.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(ref)});
                    }
                    formula = s.formula;
                    source = .{ .step = .{ .id = sid, .loc = ref.start } };
                },
                .block => return self.fail(ref.start, "'{s}' names a subproof; simplify takes equations", .{self.text(ref)}),
            } else {
                const stmt_id = try self.resolveStatementRef(ref);
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                switch (stmt) {
                    .axiom => |a| {
                        if (a.is_hole) try self.inheritHoles(a.holes);
                        formula = a.formula;
                        source = .{ .axiom = .{ .id = stmt_id, .loc = ref.start } };
                    },
                    .theorem => |t| {
                        if (!t.proven) return self.fail(ref.start, "cites unproven theorem '{s}'", .{self.text(ref)});
                        try self.inheritAccelerated(t.accelerated);
                        try self.inheritHoles(t.holes);
                        formula = t.formula;
                        source = .{ .theorem = .{ .id = stmt_id, .loc = ref.start } };
                    },
                    .schema => return self.fail(ref.start, "'{s}' is a schema; simplify takes equations", .{self.text(ref)}),
                }
            }
            switch (try self.equationRule(formula, source)) {
                .rule => |r| try rules.append(self.arena, r),
                .not_equation => return self.fail(ref.start, "'{s}' is not an equation", .{self.text(ref)}),
                .binder_missing => return self.fail(ref.start, "'{s}': not every bound variable occurs on the left-hand side", .{self.text(ref)}),
            }
        }

        const s = goal_node.eq.lhs;
        const t = goal_node.eq.rhs;
        if (self.pool.alphaEq(s, t)) return .reflexivity;

        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules.items, s, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "simplify: rewrite limit reached (looping rule set?)", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules.items, t, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "simplify: rewrite limit reached (looping rule set?)", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        if (!self.pool.alphaEq(rs.nf, rt.nf)) {
            return self.fail(loc, "simplify: normal forms differ: '{s}' vs '{s}'", .{
                try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
            });
        }
        return self.emitJoin(low, emit_block, loc, rules.items, s, t, rs, rt);
    }

    // --- the `ac` tactic: associative-commutative reordering (emits kernel steps) ---
    // Proves s = t when both are sums (over `add`) with the same multiset of
    // opaque atoms, differing only by associativity/commutativity. Each side
    // is re-associated to a right-nested comb (via addIsAssociative as a
    // terminating rewrite), its atoms flattened and bubble-sorted into a
    // canonical order (via addLeftSwap/addIsCommutative, one fabricated
    // rewrite per transposition — the sortTrace machinery), then the two
    // canonical forms are joined. All kernel-checked; no accelerated step.

    /// Flatten an `add`-tree into its atom summands (any maximal subterm that
    /// is not itself an `add(_, _)`), left-to-right.
    fn flattenSum(self: *Elaborator, add_sym: term.SymId, t: TermId, out: *std.ArrayList(TermId)) ElabError!void {
        const node = self.pool.get(t);
        if (node == .app and symIs(node.app.sym, add_sym) and node.app.args_len == 2) {
            // copy arg ids before recursing: pool.args aliases pool.extra, so a
            // walk that grows the pool would dangle the slice (see polyMonomials).
            const args = self.pool.args(node.app);
            const a0 = args[0];
            const a1 = args[1];
            try self.flattenSum(add_sym, a0, out);
            try self.flattenSum(add_sym, a1, out);
            return;
        }
        try out.append(self.arena, t);
    }

    fn acJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const goal_node = self.pool.get(goal);
        if (goal_node != .eq) {
            if (goal_node == .quant and goal_node.quant.q == .forall) {
                return self.fail(loc, "assoc_commut proves equations; use assoc_commut_quantified for a 'forall …; s = t' goal", .{});
            }
            return self.fail(loc, "assoc_commut proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
        }
        return self.acEquation(low, block_id, loc, goal, c.args, c.refs);
    }

    /// `ac` peeling the forall prefix: fix the binders, run the ac core on the
    /// equation body, close with forall_intro. Mirrors simplify_quantified.
    fn acQuantifiedJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const goal_node = self.pool.get(goal);
        if (goal_node != .quant or goal_node.quant.q != .forall) {
            if (goal_node == .eq) {
                return self.fail(loc, "assoc_commut_quantified expects a quantified goal; did you mean assoc_commut?", .{});
            }
            return self.fail(loc, "assoc_commut_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
        }
        const u = try self.peelUniversal(goal, "ac");
        if (self.pool.get(u.body) != .eq) {
            return self.fail(loc, "assoc_commut_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
        }
        const opened = try self.openUniversal(low, block_id, u);
        const body_just = try self.acEquation(low, opened.innermost, loc, u.body, c.args, c.refs);
        return self.closeUniversal(low, loc, u, opened.blocks, body_just);
    }

    /// The ac core on a bare equation goal `goal` emitted in `block_id`:
    /// pick the operator, resolve its AC lemma triple, bubble-sort both sides,
    /// emit the join. Shared by `ac` and `ac_quantified`. `refs` are optional
    /// pre-normalization lemmas (e.g. distributivity) applied L→R to each side
    /// before flattening — so `mul(add(a,b),c) = add(mul(b,c),mul(a,c))` is
    /// distributed then AC-sorted.
    fn acEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, goal: TermId, args: []const *const ast.Expr, refs: []const lexer.Token) ElabError!kernel.Justification {
        const goal_node = self.pool.get(goal);
        const s0 = goal_node.eq.lhs;
        const t0 = goal_node.eq.rhs;

        // exactly two forms: bare `assoc_commut` (well-known add/mul triple), or
        // `assoc_commut(assoc, comm, swap)` (an explicit AC triple for a custom
        // operator). No partials — 1 or 2 args is an error.
        if (args.len != 0 and args.len != 3) {
            return self.fail(loc, "assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got {d}", .{args.len});
        }
        const explicit = args.len == 3;

        // optional pre-normalization rules (distributivity etc.), resolved from
        // the cited refs and applied L→R to each side before flattening. Their
        // rule indices sit at the FRONT of the combined `rules` array so the
        // AC bubble-sort's indices (assoc=0…) shift after them.
        var rules: std.ArrayList(simplify_mod.Rule) = .empty;
        for (refs) |ref| {
            try rules.append(self.arena, try self.resolveRewriteRule(low, block_id, ref, "assoc_commut"));
        }
        const pre_count = rules.items.len;
        const pre_rules = rules.items[0..pre_count];

        // distribute both sides (L→R with the pre-rules); the AC operator is
        // detected on the distributed LHS. Traces feed emitJoin unchanged.
        const s_pre = simplify_mod.normalize(self.arena, self.pool, self.env, pre_rules, s0, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "assoc_commut: pre-normalization rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const t_pre = simplify_mod.normalize(self.arena, self.pool, self.env, pre_rules, t0, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "assoc_commut: pre-normalization rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const s = s_pre.nf;
        const t = t_pre.nf;

        // Resolve the AC triple + its operator. Explicit form: resolve the three
        // cited lemmas and recover the operator from the commutativity lemma's
        // shape (`f(a,b) = f(b,a)` → `f`). Bare form: pick add/mul from the goal
        // LHS head and resolve their well-known triple.
        const assoc_idx = rules.items.len;
        var op_sym: term.SymId = undefined;
        if (explicit) {
            const a_rule = try self.acArgRule(low, block_id, args[0]);
            const c_rule = try self.acArgRule(low, block_id, args[1]);
            const w_rule = try self.acArgRule(low, block_id, args[2]);
            // operator = head symbol of the commutativity lemma's LHS
            const c_lhs = self.pool.get(c_rule.lhs);
            if (c_lhs != .app or c_lhs.app.args_len != 2) {
                return self.fail(exprLoc(args[1]), "assoc_commut: the commutativity lemma must have shape 'f(a, b) = f(b, a)'", .{});
            }
            op_sym = c_lhs.app.sym;
            try rules.append(self.arena, a_rule);
            try rules.append(self.arena, c_rule);
            try rules.append(self.arena, w_rule);
        } else {
            const add_sym = try self.wellKnownSym("add");
            const mul_sym = try self.wellKnownSym("mul");
            const s_head: ?term.SymId = if (self.pool.get(s) == .app) self.pool.get(s).app.sym else null;
            const op: struct { sym: term.SymId, assoc: []const u8, comm: []const u8, swap: []const u8 } = blk: {
                if (add_sym != null and s_head != null and s_head.? == add_sym.?) {
                    break :blk .{ .sym = add_sym.?, .assoc = "addIsAssociative", .comm = "addIsCommutative", .swap = "addLeftSwap" };
                }
                if (mul_sym != null and s_head != null and s_head.? == mul_sym.?) {
                    break :blk .{ .sym = mul_sym.?, .assoc = "mulIsAssociative", .comm = "mulIsCommutative", .swap = "mulLeftSwap" };
                }
                return self.fail(loc, "assoc_commut reorders an add- or mul-sum; the goal's left side is '{s}'", .{try self.renderTerm(s)});
            };
            op_sym = op.sym;
            // --fast: the ACCELERATED path (bare form only — an explicit triple
            // is checkable, so it always elaborates). Decide AC-equality by
            // comparing the sorted multiset of summands — NO assoc/comm/swap
            // lemmas resolved, so it works on a theory too thin to elaborate,
            // but TRUSTS the operator is associative-commutative (the theory's
            // laws are never checked). That presumption about an uncontrolled
            // symbol is why it is accelerated, not kernel-checked.
            if (!self.verify.certify_arithmetic) {
                var s_leaves: std.ArrayList(TermId) = .empty;
                var t_leaves: std.ArrayList(TermId) = .empty;
                try self.flattenSum(op_sym, s, &s_leaves);
                try self.flattenSum(op_sym, t, &t_leaves);
                self.sortTerms(s_leaves.items);
                self.sortTerms(t_leaves.items);
                const s_nf = try self.buildRightNested(op_sym, s_leaves.items);
                const t_nf = try self.buildRightNested(op_sym, t_leaves.items);
                if (!self.pool.alphaEq(s_nf, t_nf)) {
                    return self.fail(loc, "assoc_commut: sides have different summands: '{s}' vs '{s}'", .{
                        try self.renderTerm(s_nf), try self.renderTerm(t_nf),
                    });
                }
                const name = self.interner.intern("assoc_commut") catch return error.OutOfMemory;
                try self.recordAccelerated(name, loc);
                return .{ .accelerated = name };
            }
            // append the well-known triple.
            const assoc = (try self.wellKnownRule(op.assoc, loc)) orelse
                return self.fail(loc, "assoc_commut: needs {s} in scope", .{op.assoc});
            try rules.append(self.arena, assoc);
            const comm = (try self.wellKnownRule(op.comm, loc)) orelse
                return self.fail(loc, "assoc_commut: needs {s} in scope", .{op.comm});
            try rules.append(self.arena, comm);
            const swap = (try self.wellKnownRule(op.swap, loc)) orelse
                return self.fail(loc, "assoc_commut: needs {s} in scope", .{op.swap});
            try rules.append(self.arena, swap);
        }
        const comm_idx = assoc_idx + 1;
        const swap_idx = assoc_idx + 2;

        const ac_symbols: presburger_mod.Symbols = .{ .add = op_sym };

        // per side: re-associate to a right-nested comb, flatten, bubble-sort.
        // `assoc_idx` is where associativity landed after the pre-rules.
        const plan = (try self.acPlan(ac_symbols, rules.items, assoc_idx, comm_idx, swap_idx, op_sym, s)) orelse
            return error.OutOfMemory;
        const plan_t = (try self.acPlan(ac_symbols, rules.items, assoc_idx, comm_idx, swap_idx, op_sym, t)) orelse
            return error.OutOfMemory;
        if (!self.pool.alphaEq(plan.sorted, plan_t.sorted)) {
            return self.fail(loc, "assoc_commut: sides have different summands: '{s}' vs '{s}'", .{
                try self.renderTerm(plan.sorted), try self.renderTerm(plan_t.sorted),
            });
        }
        // prepend the distribution trace (s0 -> s) so emitJoin replays the full
        // chain s0 -> distributed -> sorted against the combined rules.
        const full_s = try self.concatTrace(s_pre.trace, plan.trace);
        const full_t = try self.concatTrace(t_pre.trace, plan_t.trace);
        return self.emitJoin(low, block_id, loc, rules.items, s0, t0, .{ .nf = plan.sorted, .trace = full_s }, .{ .nf = plan_t.sorted, .trace = full_t });
    }

    fn concatTrace(self: *Elaborator, a: []const simplify_mod.Rewrite, b: []const simplify_mod.Rewrite) ElabError![]const simplify_mod.Rewrite {
        if (a.len == 0) return b;
        if (b.len == 0) return a;
        var out: std.ArrayList(simplify_mod.Rewrite) = .empty;
        try out.appendSlice(self.arena, a);
        try out.appendSlice(self.arena, b);
        return out.items;
    }

    // -- the `assoc` tactic (associativity-only reorder) --------------------
    //
    // Proves `s = t` when both are equal by ASSOCIATIVITY ALONE of a single
    // operator — the non-commutative sibling of `assoc_commut`. Right-nests each
    // side (associativity is confluent + terminating, so right-nesting is a
    // canonical form) and compares; no reordering, no commutativity. The
    // associativity lemma is REQUIRED as the sole argument — there is no bare
    // form and no assumption the operator is add/mul; the operator is recovered
    // from the lemma's shape `f(f(a,b),c) = f(a,f(b,c))`.

    fn assocJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const goal_node = self.pool.get(goal);
        if (goal_node != .eq) {
            if (goal_node == .quant and goal_node.quant.q == .forall) {
                return self.fail(loc, "assoc proves equations; use assoc_quantified for a 'forall …; s = t' goal", .{});
            }
            return self.fail(loc, "assoc proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
        }
        return self.assocEquation(low, block_id, loc, goal, c.args);
    }

    fn assocQuantifiedJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const goal_node = self.pool.get(goal);
        if (goal_node != .quant or goal_node.quant.q != .forall) {
            if (goal_node == .eq) {
                return self.fail(loc, "assoc_quantified expects a quantified goal; did you mean assoc?", .{});
            }
            return self.fail(loc, "assoc_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
        }
        const u = try self.peelUniversal(goal, "assoc");
        if (self.pool.get(u.body) != .eq) {
            return self.fail(loc, "assoc_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
        }
        const opened = try self.openUniversal(low, block_id, u);
        const body_just = try self.assocEquation(low, opened.innermost, loc, u.body, c.args);
        return self.closeUniversal(low, loc, u, opened.blocks, body_just);
    }

    fn assocEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, goal: TermId, args: []const *const ast.Expr) ElabError!kernel.Justification {
        // REQUIRED: exactly one argument, the associativity lemma.
        if (args.len != 1) {
            return self.fail(loc, "assoc requires an associativity lemma: assoc(<assocLemma>); got {d} argument(s)", .{args.len});
        }
        const rule = try self.acArgRule(low, block_id, args[0]);
        // the operator is the head of the lemma's LHS `f(f(a,b),c)` → `f`;
        // verify the shape and that LHS and RHS share that head.
        const l = self.pool.get(rule.lhs);
        if (l != .app or l.app.args_len != 2) {
            return self.fail(exprLoc(args[0]), "assoc: the associativity lemma must have shape 'f(f(a, b), c) = f(a, f(b, c))'", .{});
        }
        const op_sym = l.app.sym;
        const r = self.pool.get(rule.rhs);
        if (r != .app or r.app.sym != op_sym) {
            return self.fail(exprLoc(args[0]), "assoc: the associativity lemma's two sides must share the operator", .{});
        }

        const goal_node = self.pool.get(goal);
        const s0 = goal_node.eq.lhs;
        const t0 = goal_node.eq.rhs;

        // one-rule array so emitJoin's rule_idx (0) lines up.
        const rules = [_]simplify_mod.Rule{rule};

        // --fast: the accelerated assoc path. Structurally right-nest both
        // sides over the operator and compare — WITHOUT emitting the kernel
        // rewrite chain, presuming associativity rather than discharging it.
        // Accelerated, not kernel-checked.
        if (!self.verify.certify_arithmetic) {
            var s_leaves: std.ArrayList(TermId) = .empty;
            var t_leaves: std.ArrayList(TermId) = .empty;
            try self.flattenSum(op_sym, s0, &s_leaves);
            try self.flattenSum(op_sym, t0, &t_leaves);
            const s_nf = try self.buildRightNested(op_sym, s_leaves.items);
            const t_nf = try self.buildRightNested(op_sym, t_leaves.items);
            if (!self.pool.alphaEq(s_nf, t_nf)) {
                return self.fail(loc, "assoc: sides differ by more than associativity: '{s}' vs '{s}'", .{
                    try self.renderTerm(s_nf), try self.renderTerm(t_nf),
                });
            }
            const name = self.interner.intern("assoc") catch return error.OutOfMemory;
            try self.recordAccelerated(name, loc);
            return .{ .accelerated = name };
        }

        // certify: right-nest each side by the associativity rule (terminating),
        // compare the canonical forms, emit the join.
        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, &rules, s0, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "assoc: rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, &rules, t0, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "assoc: rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        if (!self.pool.alphaEq(rs.nf, rt.nf)) {
            return self.fail(loc, "assoc: sides differ by more than associativity: '{s}' vs '{s}'", .{
                try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
            });
        }
        return self.emitJoin(low, block_id, loc, &rules, s0, t0, rs, rt);
    }

    // -- the `polynomial` tactic (nonlinear identities, emits kernel steps) ---------
    //
    // Proves `s = t` when both are polynomials over add/mul with the same
    // expansion. The nonlinear analogue of `ac`: canonicalize each side to a
    // sorted sum of sorted monomials, then join. Elaborated — emits a
    // ring-rewrite certificate (no accelerated step). Reuses the ac machinery: `normalize` for the
    // terminating distribute/fold passes, `acPlan` for the two sorts.

    /// Resolve the optional `(theory)` argument, scoping `theory_file` for the
    /// duration of the caller (via the returned saved value + defer at the call
    /// site). `polynomial(<module>)` resolves the ring vocabulary + lemmas
    /// against that module's scope; bare `polynomial` resolves locally.
    fn enterTheory(self: *Elaborator, c: ast.Step.Claim) ElabError!void {
        if (c.schema) |theory_tok| {
            const ns = try self.internTok(theory_tok);
            self.theory_file = self.env.findNamespace(self.file, ns) orelse
                return self.fail(theory_tok.start, "unknown theory '{s}' (not an imported module)", .{self.text(theory_tok)});
        }
    }

    fn polynomialJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const goal_node = self.pool.get(goal);
        if (goal_node != .eq) {
            if (goal_node == .quant and goal_node.quant.q == .forall) {
                return self.fail(loc, "polynomial proves equations; use polynomial_quantified for a 'forall …; s = t' goal", .{});
            }
            return self.fail(loc, "polynomial proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
        }
        const saved_theory = self.theory_file;
        defer self.theory_file = saved_theory;
        try self.enterTheory(c);
        return self.polynomialEquation(low, block_id, loc, goal);
    }

    /// `polynomial` peeling the forall prefix — mirrors ac_quantified.
    fn polynomialQuantifiedJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const goal_node = self.pool.get(goal);
        if (goal_node != .quant or goal_node.quant.q != .forall) {
            if (goal_node == .eq) {
                return self.fail(loc, "polynomial_quantified expects a quantified goal; did you mean polynomial?", .{});
            }
            return self.fail(loc, "polynomial_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
        }
        const saved_theory = self.theory_file;
        defer self.theory_file = saved_theory;
        try self.enterTheory(c);
        const u = try self.peelUniversal(goal, "poly");
        if (self.pool.get(u.body) != .eq) {
            return self.fail(loc, "polynomial_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
        }
        const opened = try self.openUniversal(low, block_id, u);
        const body_just = try self.polynomialEquation(low, opened.innermost, loc, u.body);
        return self.closeUniversal(low, loc, u, opened.blocks, body_just);
    }

    /// The set of well-known rules `polynomial` needs, resolved as one array
    /// with named index ranges. Distribution + identity/zero folding are the
    /// terminating `normalize` rules; the per-operator triples drive the sorts.
    const PolyRules = struct {
        rules: []const simplify_mod.Rule,
        /// distribute + fold rules run via normalize (indices [0, fold_end))
        fold_end: usize,
        mul_assoc: usize,
        mul_comm: usize,
        mul_swap: usize,
        add_assoc: usize,
        add_comm: usize,
        add_swap: usize,
        add_sym: term.SymId,
        mul_sym: term.SymId,
    };

    fn polyRules(self: *Elaborator, loc: u32) ElabError!?PolyRules {
        const add_sym = (try self.wellKnownSym("add")) orelse return null;
        const mul_sym = (try self.wellKnownSym("mul")) orelse return null;
        var rules: std.ArrayList(simplify_mod.Rule) = .empty;
        // terminating expand/fold rules (distribution shrinks mul-over-add
        // nesting; the identity/zero folds shrink term size), run to fixpoint
        // by `normalize` before either sort.
        const fold_names = [_][]const u8{
            "mulAddDistribLeft", "mulAddDistribRight",
            "mulOneLeft",        "mulOneRight",
            "mulZeroLeft",       "mulZeroRight",
            "addZeroLeft",       "addZeroRight",
        };
        for (fold_names) |nm| {
            const r = (try self.wellKnownRule(nm, loc)) orelse
                return self.fail(loc, "polynomial: needs {s} in scope", .{nm});
            try rules.append(self.arena, r);
        }
        const fold_end = rules.items.len;
        // the two operator triples (assoc/comm/swap), appended after the folds.
        const triples = [_]struct { assoc: []const u8, comm: []const u8, swap: []const u8 }{
            .{ .assoc = "mulIsAssociative", .comm = "mulIsCommutative", .swap = "mulLeftSwap" },
            .{ .assoc = "addIsAssociative", .comm = "addIsCommutative", .swap = "addLeftSwap" },
        };
        var idx: [6]usize = undefined;
        var w: usize = 0;
        for (triples) |tr| {
            inline for (.{ tr.assoc, tr.comm, tr.swap }) |nm| {
                idx[w] = rules.items.len;
                const r = (try self.wellKnownRule(nm, loc)) orelse
                    return self.fail(loc, "polynomial: needs {s} in scope", .{nm});
                try rules.append(self.arena, r);
                w += 1;
            }
        }
        return .{
            .rules = rules.items,
            .fold_end = fold_end,
            .mul_assoc = idx[0], .mul_comm = idx[1], .mul_swap = idx[2],
            .add_assoc = idx[3], .add_comm = idx[4], .add_swap = idx[5],
            .add_sym = add_sym, .mul_sym = mul_sym,
        };
    }

    /// Lift a sub-term trace into whole-term context: each entry rewrites a
    /// SUBTERM (a single monomial in the sum), but `emitSideChain` states each
    /// intermediate as an equation over the WHOLE term. The kernel rewrite is
    /// by instance (`inst_lhs`→`inst_rhs`), which is context-free, so only the
    /// recorded `before`/`after` whole-terms need rebuilding: substitute the
    /// evolving subterm back into the sum at position `i`. `others` holds every
    /// monomial except `i` (already in final form for indices < i, original for
    /// indices > i); `ctx(sub)` = the sum with slot `i` = `sub`.
    fn liftMonoTrace(
        self: *Elaborator,
        add_symbols: presburger_mod.Symbols,
        before: []const TermId,
        after: []const TermId,
        sub_trace: []const simplify_mod.Rewrite,
        out: *std.ArrayList(simplify_mod.Rewrite),
    ) ElabError!bool {
        // scratch slot list = before ++ [hole] ++ after; the hole is filled per
        // entry to rebuild the whole-term before/after.
        var slots: std.ArrayList(TermId) = .empty;
        try slots.appendSlice(self.arena, before);
        const hole = slots.items.len;
        try slots.append(self.arena, sub_trace[0].before); // placeholder, overwritten per entry
        try slots.appendSlice(self.arena, after);
        for (sub_trace) |rw| {
            slots.items[hole] = rw.before;
            const w_before = (try self.buildComb(add_symbols, slots.items)) orelse return false;
            slots.items[hole] = rw.after;
            const w_after = (try self.buildComb(add_symbols, slots.items)) orelse return false;
            try out.append(self.arena, .{
                .before = w_before,
                .after = w_after,
                .rule_idx = rw.rule_idx,
                .bindings = rw.bindings,
                .inst_lhs = rw.inst_lhs,
                .inst_rhs = rw.inst_rhs,
            });
        }
        return true;
    }

    /// Canonicalize one side to a sorted-sum-of-sorted-monomials normal form,
    /// accumulating the full replayable trace against `pr.rules`.
    fn polyCanon(self: *Elaborator, pr: PolyRules, x: TermId) ElabError!?simplify_mod.Result {
        // 1) distribute + fold to a flat sum of monomials (terminating). Its
        //    trace is already whole-term (normalize over `x`).
        const fold_rules = pr.rules[0..pr.fold_end];
        const dist = simplify_mod.normalize(self.arena, self.pool, self.env, fold_rules, x, 4000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        var trace: std.ArrayList(simplify_mod.Rewrite) = .empty;
        try trace.appendSlice(self.arena, dist.trace);

        const add_symbols: presburger_mod.Symbols = .{ .add = pr.add_sym };
        const mul_symbols: presburger_mod.Symbols = .{ .add = pr.mul_sym };

        // 2) RIGHT-NEST the outer sum first (add-associativity only,
        //    terminating). This makes the running term a right-nested comb, so
        //    the `buildComb` contexts used to lift the per-monomial traces
        //    below match the real term shape exactly.
        const add_assoc_only = pr.rules[pr.add_assoc .. pr.add_assoc + 1];
        const rn = simplify_mod.normalize(self.arena, self.pool, self.env, add_assoc_only, dist.nf, 4000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        // rebase this single-rule trace's rule_idx to the full-array index.
        for (rn.trace) |rw| {
            var r = rw;
            r.rule_idx = rw.rule_idx + pr.add_assoc;
            try trace.append(self.arena, r);
        }

        // 3) sort each monomial's factors (mul-acPlan), lifting each sub-trace
        //    into the (right-nested) whole-sum context so the chain stays
        //    whole-term.
        var monos: std.ArrayList(TermId) = .empty;
        try self.flattenSum(pr.add_sym, rn.nf, &monos);
        var sorted_monos: std.ArrayList(TermId) = .empty;
        for (monos.items, 0..) |m, i| {
            const mp = (try self.acPlan(mul_symbols, pr.rules, pr.mul_assoc, pr.mul_comm, pr.mul_swap, pr.mul_sym, m)) orelse return null;
            if (mp.trace.len > 0) {
                // context: [sorted_0..sorted_{i-1}] ++ hole ++ [mono_{i+1}..]
                const lifted = try self.liftMonoTrace(add_symbols, sorted_monos.items, monos.items[i + 1 ..], mp.trace, &trace);
                if (!lifted) return null;
            }
            try sorted_monos.append(self.arena, mp.sorted);
        }
        const mono_sum = (try self.buildComb(add_symbols, sorted_monos.items)) orelse return null;

        // 4) bubble-sort the sum of monomials. The sum is already right-nested,
        //    so run only the sort phase (sortTrace), not acPlan's re-nest.
        var leaves: std.ArrayList(TermId) = .empty;
        try self.flattenSum(pr.add_sym, mono_sum, &leaves);
        const sorted = (try self.sortTrace(add_symbols, pr.rules, pr.add_comm, pr.add_swap, .{ .succs = 0, .leaves = leaves.items }, &trace)) orelse return null;
        return .{ .nf = sorted, .trace = trace.items };
    }

    fn polynomialEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, goal: TermId) ElabError!kernel.Justification {
        const goal_node = self.pool.get(goal);
        const s0 = goal_node.eq.lhs;
        const t0 = goal_node.eq.rhs;

        // --fast: the accelerated polynomial path. Decide equality by comparing
        // the bare syntactic semiring normal forms — NO theory lemmas consulted,
        // so it works on a theory too thin to elaborate, but it TRUSTS that
        // add/mul are a commutative semiring (the theory's own laws are never
        // checked). That presumption about uncontrolled symbols is exactly why
        // it is accelerated, not kernel-checked. The default path below discharges
        // the same presumption against the kernel.
        if (!self.verify.certify_arithmetic) {
            const add_sym = (try self.wellKnownSym("add")) orelse
                return self.fail(loc, "polynomial: arithmetic vocabulary (add, mul) not in scope", .{});
            const mul_sym = (try self.wellKnownSym("mul")) orelse
                return self.fail(loc, "polynomial: arithmetic vocabulary (add, mul) not in scope", .{});
            const zero_sym = try self.wellKnownSym("ZERO");
            const one_sym = try self.wellKnownSym("ONE");
            const ns = PolyNorm{ .add_sym = add_sym, .mul_sym = mul_sym, .zero_sym = zero_sym, .one_sym = one_sym };
            const ns_s = try self.polyNormForm(ns, s0);
            const ns_t = try self.polyNormForm(ns, t0);
            if (!self.pool.alphaEq(ns_s, ns_t)) {
                return self.fail(loc, "polynomial: sides expand differently: '{s}' vs '{s}'", .{
                    try self.renderTerm(ns_s), try self.renderTerm(ns_t),
                });
            }
            const name = self.interner.intern("polynomial") catch return error.OutOfMemory;
            try self.recordAccelerated(name, loc);
            return .{ .accelerated = name };
        }

        // default: the kernel-checked certificate — resolve the ring lemmas,
        // canonicalize both sides recording a replayable trace, and emit the
        // kernel join.
        const pr = (try self.polyRules(loc)) orelse
            return self.fail(loc, "polynomial: arithmetic vocabulary (add, mul) not in scope", .{});

        const rs = (try self.polyCanon(pr, s0)) orelse
            return self.fail(loc, "polynomial: could not canonicalize '{s}'", .{try self.renderTerm(s0)});
        const rt = (try self.polyCanon(pr, t0)) orelse
            return self.fail(loc, "polynomial: could not canonicalize '{s}'", .{try self.renderTerm(t0)});
        if (!self.pool.alphaEq(rs.nf, rt.nf)) {
            return self.fail(loc, "polynomial: sides expand differently: '{s}' vs '{s}'", .{
                try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
            });
        }
        return self.emitJoin(low, block_id, loc, pr.rules, s0, t0, rs, rt);
    }

    // -- the accelerated polynomial path's lemma-free canonical form --------
    //
    // A bare structural semiring normalizer: it flattens/sorts add and mul
    // trees ASSUMING commutativity, associativity, distributivity, and 0/1
    // identities hold — without resolving or citing any theory lemma. Used only
    // by the --fast accelerated path (the default path elaborates via resolved
    // lemmas + kernel recheck). Deterministic, so its output is a true canonical
    // form; two terms are semiring-equal iff their normal forms are alphaEq.

    const PolyNorm = struct { add_sym: term.SymId, mul_sym: term.SymId, zero_sym: ?term.SymId, one_sym: ?term.SymId };

    /// Canonicalize `x` to a sorted sum of sorted monomials. Recursion:
    /// normalize children, distribute mul over add, sort, fold 0/1.
    fn polyNormForm(self: *Elaborator, ns: PolyNorm, x: TermId) ElabError!TermId {
        // gather the sum's monomials (each a normalized product of atoms),
        // sort by termOrder, drop ZERO terms, rebuild right-nested.
        var monos: std.ArrayList(TermId) = .empty;
        try self.polyMonomials(ns, x, &monos);
        // drop additive ZEROs
        var kept: std.ArrayList(TermId) = .empty;
        for (monos.items) |m| {
            if (ns.zero_sym != null and self.isSym(m, ns.zero_sym.?)) continue;
            try kept.append(self.arena, m);
        }
        if (kept.items.len == 0) {
            // empty sum = ZERO (or x itself if no ZERO symbol known)
            if (ns.zero_sym) |z| return try self.pool.addApp(.app, z, &.{});
            return x;
        }
        self.sortTerms(kept.items);
        return try self.buildRightNested(ns.add_sym, kept.items);
    }

    /// Collect the normalized monomials of `x` (the summands after full
    /// distribution), appending to `out`.
    fn polyMonomials(self: *Elaborator, ns: PolyNorm, x: TermId, out: *std.ArrayList(TermId)) ElabError!void {
        const node = self.pool.get(x);
        if (node == .app and symIs(node.app.sym, ns.add_sym) and node.app.args_len == 2) {
            const args = self.pool.args(node.app);
            const a0 = args[0];
            const a1 = args[1];
            try self.polyMonomials(ns, a0, out);
            try self.polyMonomials(ns, a1, out);
            return;
        }
        if (node == .app and symIs(node.app.sym, ns.mul_sym) and node.app.args_len == 2) {
            // distribute: (sum of A) * (sum of B) = sum over a in A, b in B of a*b.
            // COPY the arg ids out first: pool.args aliases pool.extra, and the
            // recursion below allocates product terms (polyMonomialProduct ->
            // addApp), which reallocates extra and would dangle the slice.
            const margs = self.pool.args(node.app);
            const m0 = margs[0];
            const m1 = margs[1];
            var left: std.ArrayList(TermId) = .empty;
            var right: std.ArrayList(TermId) = .empty;
            try self.polyMonomials(ns, m0, &left);
            try self.polyMonomials(ns, m1, &right);
            for (left.items) |a| {
                for (right.items) |b| {
                    try out.append(self.arena, try self.polyMonomialProduct(ns, a, b));
                }
            }
            return;
        }
        // an atom (variable, constant, or opaque application): a monomial with
        // one factor. Fold multiplicative identity later; here it stands alone.
        try out.append(self.arena, x);
    }

    /// Multiply two already-normalized monomials: flatten both into factor
    /// lists, drop ONE factors, ZERO-annihilate, sort, rebuild right-nested.
    fn polyMonomialProduct(self: *Elaborator, ns: PolyNorm, a: TermId, b: TermId) ElabError!TermId {
        var factors: std.ArrayList(TermId) = .empty;
        try self.polyFactors(ns, a, &factors);
        try self.polyFactors(ns, b, &factors);
        var kept: std.ArrayList(TermId) = .empty;
        for (factors.items) |f| {
            if (ns.zero_sym != null and self.isSym(f, ns.zero_sym.?)) {
                // a ZERO factor annihilates the whole monomial
                return try self.pool.addApp(.app, ns.zero_sym.?, &.{});
            }
            if (ns.one_sym != null and self.isSym(f, ns.one_sym.?)) continue;
            try kept.append(self.arena, f);
        }
        if (kept.items.len == 0) {
            if (ns.one_sym) |o| return try self.pool.addApp(.app, o, &.{});
            // no ONE symbol: fall back to a (both were ONE-less already)
            return a;
        }
        self.sortTerms(kept.items);
        return try self.buildRightNested(ns.mul_sym, kept.items);
    }

    /// Flatten a mul-tree into its factor list (atoms).
    fn polyFactors(self: *Elaborator, ns: PolyNorm, x: TermId, out: *std.ArrayList(TermId)) ElabError!void {
        const node = self.pool.get(x);
        if (node == .app and symIs(node.app.sym, ns.mul_sym) and node.app.args_len == 2) {
            // copy the arg ids before recursing (pool.args aliases pool.extra,
            // which downstream allocations may grow; see polyMonomials).
            const fargs = self.pool.args(node.app);
            const f0 = fargs[0];
            const f1 = fargs[1];
            try self.polyFactors(ns, f0, out);
            try self.polyFactors(ns, f1, out);
            return;
        }
        try out.append(self.arena, x);
    }

    fn isSym(self: *Elaborator, t: TermId, sym: term.SymId) bool {
        const node = self.pool.get(t);
        return node == .app and node.app.sym == sym and node.app.args_len == 0;
    }

    /// In-place insertion sort by termOrder (stable, small lists).
    fn sortTerms(self: *Elaborator, items: []TermId) void {
        var i: usize = 1;
        while (i < items.len) : (i += 1) {
            const v = items[i];
            var j = i;
            while (j > 0 and self.pool.termOrder(items[j - 1], v) == .gt) : (j -= 1) {
                items[j] = items[j - 1];
            }
            items[j] = v;
        }
    }

    fn buildRightNested(self: *Elaborator, sym: term.SymId, leaves: []const TermId) ElabError!TermId {
        var cur = leaves[leaves.len - 1];
        var i = leaves.len - 1;
        while (i > 0) {
            i -= 1;
            cur = try self.pool.addApp(.app, sym, &.{ leaves[i], cur });
        }
        return cur;
    }

    const AcPlan = struct { sorted: TermId, trace: []const simplify_mod.Rewrite };

    /// Re-associate `start` to a right-nested comb, then bubble-sort its
    /// atoms into canonical (termOrder) order, accumulating one trace.
    fn acPlan(self: *Elaborator, symbols: presburger_mod.Symbols, rules: []const simplify_mod.Rule, assoc_idx: usize, comm_idx: usize, swap_idx: usize, add_sym: term.SymId, start: TermId) ElabError!?AcPlan {
        // phase 1: right-nest via associativity only (terminating)
        const assoc_only = rules[assoc_idx .. assoc_idx + 1];
        const rn = simplify_mod.normalize(self.arena, self.pool, self.env, assoc_only, start, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        // phase 2: flatten the right-nested comb and bubble-sort
        var leaves: std.ArrayList(TermId) = .empty;
        try self.flattenSum(add_sym, rn.nf, &leaves);
        var trace: std.ArrayList(simplify_mod.Rewrite) = .empty;
        // phase-1 normalized over the single-rule slice `rules[assoc_idx..]`, so
        // its trace rule_idx is 0-relative; rebase it to the full-array index.
        for (rn.trace) |rw| {
            var r = rw;
            r.rule_idx = rw.rule_idx + assoc_idx;
            try trace.append(self.arena, r);
        }
        const sorted = (try self.sortTrace(symbols, rules, comm_idx, swap_idx, .{ .succs = 0, .leaves = leaves.items }, &trace)) orelse return null;
        return .{ .sorted = sorted, .trace = trace.items };
    }

    /// Resolve an `assoc_commut(assoc, comm, swap)` argument — a bare name
    /// expression — into a rewrite rule (reusing resolveRewriteRule's step /
    /// statement resolution + accelerated-tactic inheritance).
    fn acArgRule(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, arg: *const ast.Expr) ElabError!simplify_mod.Rule {
        if (arg.* != .name) {
            return self.fail(exprLoc(arg), "assoc_commut argument must name an equation lemma", .{});
        }
        return self.resolveRewriteRule(low, block_id, arg.name, "assoc_commut");
    }

    /// Resolve one cited ref (step label or statement) into an L→R rewrite
    /// rule, with the same accessibility/acceleration checks as simplify. `who` names
    /// the citing tactic for error messages.
    fn resolveRewriteRule(self: *Elaborator, low: *Lowering, emit_block: kernel.BlockId, ref: lexer.Token, comptime who: []const u8) ElabError!simplify_mod.Rule {
        const name = try self.internTok(ref);
        var formula: TermId = undefined;
        var source: simplify_mod.Source = undefined;
        if (low.labels.get(name)) |target| switch (target) {
            .step => |sid| {
                const s = low.steps.items[@intFromEnum(sid)];
                if (!lowAncestorOrSelf(low, s.block, emit_block)) {
                    return self.fail(ref.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(ref)});
                }
                formula = s.formula;
                source = .{ .step = .{ .id = sid, .loc = ref.start } };
            },
            .block => return self.fail(ref.start, "'{s}' names a subproof; " ++ who ++ " takes equation lemmas", .{self.text(ref)}),
        } else {
            const stmt_id = try self.resolveStatementRef(ref);
            switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
                .axiom => |a| {
                    if (a.is_hole) try self.inheritHoles(a.holes);
                    formula = a.formula;
                    source = .{ .axiom = .{ .id = stmt_id, .loc = ref.start } };
                },
                .theorem => |t| {
                    if (!t.proven) return self.fail(ref.start, "cites unproven theorem '{s}'", .{self.text(ref)});
                    try self.inheritAccelerated(t.accelerated);
                    try self.inheritHoles(t.holes);
                    formula = t.formula;
                    source = .{ .theorem = .{ .id = stmt_id, .loc = ref.start } };
                },
                .schema => return self.fail(ref.start, "'{s}' is a schema; " ++ who ++ " takes equation lemmas", .{self.text(ref)}),
            }
        }
        return switch (try self.equationRule(formula, source)) {
            .rule => |r| r,
            .not_equation => self.fail(ref.start, "'{s}' is not an equation", .{self.text(ref)}),
            .binder_missing => self.fail(ref.start, "'{s}': not every bound variable occurs on the left-hand side", .{self.text(ref)}),
        };
    }

    const RulePrep = union(enum) { rule: simplify_mod.Rule, not_equation, binder_missing };

    /// Strip a fact's forall prefix (binders become pattern fvars) into a
    /// left-to-right rewrite rule.
    fn equationRule(self: *Elaborator, formula: TermId, source: simplify_mod.Source) ElabError!RulePrep {
        var binders: std.ArrayList(simplify_mod.Binder) = .empty;
        var body = formula;
        while (true) {
            const node = self.pool.get(body);
            if (node != .quant or node.quant.q != .forall) break;
            const fresh = try self.freshNamed("p");
            const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
            body = try self.pool.open(node.quant.body, fv);
            try binders.append(self.arena, .{ .fvar = fresh, .sort = node.quant.sort });
        }
        const body_node = self.pool.get(body);
        if (body_node != .eq) return .not_equation;
        for (binders.items) |b| {
            if (!self.pool.occursFree(body_node.eq.lhs, b.fvar)) return .binder_missing;
        }
        return .{ .rule = .{
            .source = source,
            .binders = binders.items,
            .lhs = body_node.eq.lhs,
            .rhs = body_node.eq.rhs,
            .formula = formula,
        } };
    }

    /// Emit the certificate chains joining a successful two-sided
    /// normalization; returns the user's closing justification.
    fn emitJoin(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, rules: []const simplify_mod.Rule, s: TermId, t: TermId, rs: simplify_mod.Result, rt: simplify_mod.Result) ElabError!kernel.Justification {
        if (rt.trace.len == 0) {
            // t is already the shared normal form: the last rewrite of the
            // s-chain becomes the user's own justification
            std.debug.assert(rs.trace.len > 0); // alphaEq handled above
            const head = rs.trace[0 .. rs.trace.len - 1];
            const last = rs.trace[rs.trace.len - 1];
            const target: kernel.SRef = if (head.len > 0)
                try self.emitSideChain(low, block_id, loc, rules, s, head)
            else blk: {
                const refl = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = s } });
                break :blk try self.emitStep(low, block_id, loc, refl, .reflexivity);
            };
            const inst = try self.emitInstance(low, block_id, loc, rules[last.rule_idx], last.bindings);
            return .{ .rewrite = .{ .equation = inst, .target = target } };
        }
        // t moves: build t = NF, flip it to NF = t, and rewrite the s-side
        const t_end = try self.emitSideChain(low, block_id, loc, rules, t, rt.trace);
        const t_refl = try self.pool.add(.{ .eq = .{ .lhs = t, .rhs = t } });
        const t_refl_ref = try self.emitStep(low, block_id, loc, t_refl, .reflexivity);
        const t_sym_formula = try self.pool.add(.{ .eq = .{ .lhs = rt.nf, .rhs = t } });
        const t_sym = try self.emitStep(low, block_id, loc, t_sym_formula, .{ .rewrite = .{ .equation = t_end, .target = t_refl_ref } });
        const s_end: kernel.SRef = if (rs.trace.len > 0)
            try self.emitSideChain(low, block_id, loc, rules, s, rs.trace)
        else blk: {
            const refl = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = s } });
            break :blk try self.emitStep(low, block_id, loc, refl, .reflexivity);
        };
        return .{ .rewrite = .{ .equation = t_sym, .target = s_end } };
    }

    fn renderTerm(self: *Elaborator, id: TermId) ElabError![]const u8 {
        return @import("print.zig").render(self.arena, self.pool, self.env, self.interner, id) catch return error.OutOfMemory;
    }

    // --- C2: arithmetic certificates ----------------------------------------
    // Certificate stages for the `arithmetic` rule, all
    // kernel-checked. C2a: ground equations replay as simplify chains over
    // the well-known peano recursion axioms. C2b: universally-quantified
    // linear equations normalize to succ-towers over sorted sums (the
    // residual permutation is a chain of addIsCommutative/addLeftSwap
    // rewrites), and simple order goals a < b synthesize the witness
    // difference d, certify add(a, succ(d)) = b, and close with a
    // lessThanIntro instance. Anything outside — hypotheses, missing
    // lemmas, unjoinable forms — returns null and falls back to the accelerated path.

    const wk_term_rule_names = [_][]const u8{
        "addZeroLeft",  "addZeroRight",     "addSuccLeft", "addSuccRight",
        "mulZeroLeft",  "mulZeroRight",     "mulSuccLeft", "mulSuccRight",
        "oneIsSuccZero", "addIsAssociative",
    };

    const EqCert = struct {
        rules: []const simplify_mod.Rule,
        s: TermId,
        t: TermId,
        rs: simplify_mod.Result,
        rt: simplify_mod.Result,
    };

    const LtCert = struct {
        eq: EqCert,
        /// add(s, succ(d)) = t — the witness equation
        eq_formula: TermId,
        intro: simplify_mod.Rule,
        intro_args: []const TermId,
    };

    const ExistsCert = struct {
        witness: TermId,
        /// the body opened at the witness
        instance: TermId,
        inner: InnerPlan,
    };

    const InnerPlan = union(enum) { refl, eq: EqCert, lt: LtCert };

    const BodyPlan = union(enum) { inner: InnerPlan, exists: ExistsCert };

    /// Plan an unquantified certificate body: an equation or a less_than.
    fn planInner(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        term_rule_count: usize,
        comm_idx: ?usize,
        swap_idx: ?usize,
        body: TermId,
        loc: u32,
    ) ElabError!?InnerPlan {
        const node = self.pool.get(body);
        if (node == .eq) {
            if (self.pool.alphaEq(node.eq.lhs, node.eq.rhs)) return .refl;
            const eq = (try self.planEquation(symbols, rules, term_rule_count, comm_idx, swap_idx, node.eq.lhs, node.eq.rhs)) orelse return null;
            return .{ .eq = eq };
        }
        if (node == .pred and symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2) {
            const lt = (try self.planLess(symbols, rules, term_rule_count, comm_idx, swap_idx, body, loc)) orelse return null;
            return .{ .lt = lt };
        }
        return null;
    }

    fn emitInner(self: *Elaborator, low: *Lowering, block: kernel.BlockId, loc: u32, inner: InnerPlan) ElabError!kernel.Justification {
        return switch (inner) {
            .refl => .reflexivity,
            .eq => |eq| try self.emitJoin(low, block, loc, eq.rules, eq.s, eq.t, eq.rs, eq.rt),
            .lt => |lt| try self.emitLess(low, block, loc, lt),
        };
    }

    fn symIs(id: term.SymId, want: ?term.SymId) bool {
        return want != null and id == want.?;
    }

    /// Resolve a well-known fact by name in this file's scope; unproven and
    /// accelerated facts are unusable (they would poison the certificate).
    /// The scope arithmetic well-known names resolve in: the named theory
    /// module if `arithmetic(<mod>)` set one, else local scope.
    fn theoryScope(self: *const Elaborator) FileId {
        return self.theory_file orelse self.file;
    }

    fn wellKnownFact(self: *Elaborator, name_text: []const u8, loc: u32) ElabError!?struct { formula: TermId, source: simplify_mod.Source } {
        const name = self.interner.intern(name_text) catch return error.OutOfMemory;
        const stmt_id = self.env.findStatementId(self.theoryScope(), name) orelse return null;
        const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
        switch (stmt) {
            .axiom => |a| return .{ .formula = a.formula, .source = .{ .axiom = .{ .id = stmt_id, .loc = loc } } },
            .theorem => |t| {
                if (!t.proven or t.accelerated.len != 0) return null;
                return .{ .formula = t.formula, .source = .{ .theorem = .{ .id = stmt_id, .loc = loc } } };
            },
            .schema => return null,
        }
    }

    fn wellKnownRule(self: *Elaborator, name_text: []const u8, loc: u32) ElabError!?simplify_mod.Rule {
        const fact = (try self.wellKnownFact(name_text, loc)) orelse return null;
        return switch (try self.equationRule(fact.formula, fact.source)) {
            .rule => |r| r,
            else => null,
        };
    }

    /// Strip a fact's forall prefix into a pseudo-rule whose lhs/rhs are
    /// both the whole stripped body (for non-equational facts that are
    /// instantiated via matchRule + emitInstance).
    fn strippedRule(self: *Elaborator, formula: TermId, source: simplify_mod.Source) ElabError!simplify_mod.Rule {
        var binders: std.ArrayList(simplify_mod.Binder) = .empty;
        var body = formula;
        while (true) {
            const node = self.pool.get(body);
            if (node != .quant or node.quant.q != .forall) break;
            const fresh = try self.freshNamed("p");
            const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
            body = try self.pool.open(node.quant.body, fv);
            try binders.append(self.arena, .{ .fvar = fresh, .sort = node.quant.sort });
        }
        return .{ .source = source, .binders = binders.items, .lhs = body, .rhs = body, .formula = formula };
    }

    const Tower = struct { succs: usize, leaves: []const TermId };

    /// Parse succ^k(right-nested sum of variables) or succ^k(ZERO); anything
    /// else is outside the certificate fragment.
    fn parseTower(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) ElabError!?Tower {
        var succs: usize = 0;
        var cur = t;
        while (true) {
            const node = self.pool.get(cur);
            if (node == .app and symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
                succs += 1;
                cur = self.pool.args(node.app)[0];
                continue;
            }
            break;
        }
        var leaves: std.ArrayList(TermId) = .empty;
        while (true) {
            const node = self.pool.get(cur);
            if (node == .fvar) {
                try leaves.append(self.arena, cur);
                break;
            }
            if (node != .app) return null;
            if (symIs(node.app.sym, symbols.add) and node.app.args_len == 2) {
                const args = self.pool.args(node.app);
                if (self.pool.get(args[0]) != .fvar) return null; // not right-nested
                try leaves.append(self.arena, args[0]);
                cur = args[1];
                continue;
            }
            if (symIs(node.app.sym, symbols.zero) and node.app.args_len == 0) {
                if (leaves.items.len != 0) return null; // ZERO inside a sum is not normal
                break;
            }
            return null;
        }
        return .{ .succs = succs, .leaves = leaves.items };
    }

    fn buildComb(self: *Elaborator, symbols: presburger_mod.Symbols, leaves: []const TermId) ElabError!?TermId {
        if (leaves.len == 0) {
            const zero = symbols.zero orelse return null;
            return try self.pool.addApp(.app, zero, &.{});
        }
        var cur = leaves[leaves.len - 1];
        var i = leaves.len - 1;
        while (i > 0) {
            i -= 1;
            const add_sym = symbols.add orelse return null;
            cur = try self.pool.addApp(.app, add_sym, &.{ leaves[i], cur });
        }
        return cur;
    }

    fn buildTower(self: *Elaborator, symbols: presburger_mod.Symbols, succs: usize, comb: TermId) ElabError!?TermId {
        var cur = comb;
        for (0..succs) |_| {
            const succ_sym = symbols.succ orelse return null;
            cur = try self.pool.addApp(.app, succ_sym, &.{cur});
        }
        return cur;
    }


    /// Bubble-sort a tower's summands, appending one rewrite per adjacent
    /// swap (addLeftSwap inside the sum, addIsCommutative for the final
    /// pair). Returns the sorted whole term, or null when a needed sort
    /// lemma is missing or a shape assumption fails.
    fn sortTrace(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        comm_idx: ?usize,
        swap_idx: ?usize,
        tower: Tower,
        trace: *std.ArrayList(simplify_mod.Rewrite),
    ) ElabError!?TermId {
        const leaves = try self.arena.dupe(TermId, tower.leaves);
        var whole = (try self.buildTower(symbols, tower.succs, (try self.buildComb(symbols, leaves)) orelse return null)) orelse return null;
        if (leaves.len > 1) {
            for (0..leaves.len - 1) |pass| {
                for (0..leaves.len - 1 - pass) |i| {
                    if (self.pool.termOrder(leaves[i], leaves[i + 1]) != .gt) continue;
                    const tail_pair = i + 2 == leaves.len;
                    const rule_idx = (if (tail_pair) comm_idx else swap_idx) orelse return null;
                    const sub_before = (try self.buildComb(symbols, leaves[i..])) orelse return null;
                    std.mem.swap(TermId, &leaves[i], &leaves[i + 1]);
                    const sub_after = (try self.buildComb(symbols, leaves[i..])) orelse return null;
                    const after = (try self.buildTower(symbols, tower.succs, (try self.buildComb(symbols, leaves)) orelse return null)) orelse return null;
                    const rule = rules[rule_idx];
                    const bindings = (try simplify_mod.matchRule(self.arena, self.pool, self.env, rule, rule.lhs, sub_before)) orelse return null;
                    try trace.append(self.arena, .{
                        .before = whole,
                        .after = after,
                        .rule_idx = rule_idx,
                        .bindings = bindings,
                        .inst_lhs = sub_before,
                        .inst_rhs = sub_after,
                    });
                    whole = after;
                }
            }
        }
        return whole;
    }

    /// Plan a kernel-checked proof of s = t: normalize both sides with the
    /// terminating rules, then sort the residual sums. Null when the sides
    /// do not join.
    fn planEquation(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        term_rule_count: usize,
        comm_idx: ?usize,
        swap_idx: ?usize,
        s: TermId,
        t: TermId,
    ) ElabError!?EqCert {
        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], s, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], t, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const tower_s = (try self.parseTower(symbols, rs.nf)) orelse return null;
        const tower_t = (try self.parseTower(symbols, rt.nf)) orelse return null;
        if (tower_s.succs != tower_t.succs) return null;

        var trace_s: std.ArrayList(simplify_mod.Rewrite) = .empty;
        try trace_s.appendSlice(self.arena, rs.trace);
        const sorted_s = (try self.sortTrace(symbols, rules, comm_idx, swap_idx, tower_s, &trace_s)) orelse return null;
        var trace_t: std.ArrayList(simplify_mod.Rewrite) = .empty;
        try trace_t.appendSlice(self.arena, rt.trace);
        const sorted_t = (try self.sortTrace(symbols, rules, comm_idx, swap_idx, tower_t, &trace_t)) orelse return null;
        // same multiset of variables (and same tower) iff the sorted forms agree
        if (!self.pool.alphaEq(sorted_s, sorted_t)) return null;
        return .{
            .rules = rules,
            .s = s,
            .t = t,
            .rs = .{ .nf = sorted_s, .trace = trace_s.items },
            .rt = .{ .nf = sorted_t, .trace = trace_t.items },
        };
    }

    /// Plan a kernel-checked proof of less_than(s, t): synthesize the difference
    /// witness d from the normalized towers, certify add(s, succ(d)) = t,
    /// and instantiate lessThanIntro.
    fn planLess(
        self: *Elaborator,
        symbols: presburger_mod.Symbols,
        rules: []const simplify_mod.Rule,
        term_rule_count: usize,
        comm_idx: ?usize,
        swap_idx: ?usize,
        body: TermId,
        loc: u32,
    ) ElabError!?LtCert {
        const pred = self.pool.get(body).pred;
        const pred_args = self.pool.args(pred);
        const s = pred_args[0];
        const t = pred_args[1];
        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], s, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules[0..term_rule_count], t, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        const tower_s = (try self.parseTower(symbols, rs.nf)) orelse return null;
        const tower_t = (try self.parseTower(symbols, rt.nf)) orelse return null;
        if (tower_t.succs < tower_s.succs + 1) return null;

        // multiset difference t - s: every s-leaf must be consumed
        var remaining: std.ArrayList(TermId) = .empty;
        try remaining.appendSlice(self.arena, tower_t.leaves);
        for (tower_s.leaves) |sl| {
            const found = for (remaining.items, 0..) |rl, i| {
                if (self.pool.termOrder(rl, sl) == .eq) break i;
            } else return null;
            _ = remaining.swapRemove(found);
        }

        const d_comb = (try self.buildComb(symbols, remaining.items)) orelse return null;
        const d = (try self.buildTower(symbols, tower_t.succs - tower_s.succs - 1, d_comb)) orelse return null;
        const succ_sym = symbols.succ orelse return null;
        const add_sym = symbols.add orelse return null;
        const succ_d = try self.pool.addApp(.app, succ_sym, &.{d});
        const eq_lhs = try self.pool.addApp(.app, add_sym, &.{ s, succ_d });
        const eq = (try self.planEquation(symbols, rules, term_rule_count, comm_idx, swap_idx, eq_lhs, t)) orelse return null;
        const eq_formula = try self.pool.add(.{ .eq = .{ .lhs = eq_lhs, .rhs = t } });

        // lessThanIntro, matched structurally so any binder order works
        const intro_fact = (try self.wellKnownFact("lessThanIntro", loc)) orelse return null;
        const intro = try self.strippedRule(intro_fact.formula, intro_fact.source);
        const implication = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = eq_formula, .rhs = body } });
        const intro_args = (try simplify_mod.matchRule(self.arena, self.pool, self.env, intro, intro.lhs, implication)) orelse return null;
        return .{ .eq = eq, .eq_formula = eq_formula, .intro = intro, .intro_args = intro_args };
    }

    fn emitLess(self: *Elaborator, low: *Lowering, block: kernel.BlockId, loc: u32, lt: LtCert) ElabError!kernel.Justification {
        const eq_just = try self.emitJoin(low, block, loc, lt.eq.rules, lt.eq.s, lt.eq.t, lt.eq.rs, lt.eq.rt);
        const eq_ref = try self.emitStep(low, block, loc, lt.eq_formula, eq_just);
        const imp_ref = try self.emitInstance(low, block, loc, lt.intro, lt.intro_args);
        return .{ .modus_ponens = .{ .implication = imp_ref, .antecedent = eq_ref } };
    }

    /// A cited hypothesis prepared for certificate use. A less_than premise
    /// contributes its witness equation (via lessThanElim + unpack) as a
    /// ground rewrite rule t0 -> add(s0, succ(w)); an equation premise is a
    /// ground rule directly.
    const CertStatement = struct { id: StatementId, is_axiom: bool };

    const CertPremise = struct {
        formula: TermId,
        /// null = statement citation, emitted at certificate time
        step: ?kernel.SRef,
        statement: ?CertStatement,
        /// index of this premise's ground rule in the rule array (its
        /// source sref is patched in during emission)
        rule_idx: usize,
        /// less_than premises only: the elim/unpack plan
        elim: ?struct {
            rule: simplify_mod.Rule,
            args: []const TermId,
            /// the instantiated implication and its existential consequent
            implication: TermId,
            exists_formula: TermId,
            w: term.Node.Fvar,
            /// the existential body opened at w, and its flip
            opened_eq: TermId,
            sym_formula: TermId,
        },
    };

    fn containsSubterm(self: *const Elaborator, hay: TermId, needle: TermId) bool {
        if (self.pool.alphaEq(hay, needle)) return true;
        switch (self.pool.get(hay)) {
            .bvar, .fvar => return false,
            .app, .pred => |a| {
                for (self.pool.args(a)) |arg| {
                    if (self.containsSubterm(arg, needle)) return true;
                }
                return false;
            },
            .eq => |p| return self.containsSubterm(p.lhs, needle) or self.containsSubterm(p.rhs, needle),
            .not => |inner| return self.containsSubterm(inner, needle),
            .bin => |b| return self.containsSubterm(b.lhs, needle) or self.containsSubterm(b.rhs, needle),
            .quant => |q| return self.containsSubterm(q.body, needle),
        }
    }

    fn arithmeticCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols) ElabError!?kernel.Justification {
        const loc = c.rule.start;

        // resolve the cited hypotheses (resolvePremises already validated
        // accessibility and existence on the accelerated path)
        var premises: std.ArrayList(CertPremise) = .empty;
        for (c.refs) |ref| {
            const name = try self.internTok(ref);
            var formula: TermId = undefined;
            var step: ?kernel.SRef = null;
            var statement: ?CertStatement = null;
            if (low.labels.get(name)) |target| {
                const sid = target.step;
                formula = low.steps.items[@intFromEnum(sid)].formula;
                step = .{ .id = sid, .loc = ref.start };
            } else {
                const stmt_id = try self.resolveStatementRef(ref);
                switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
                    .axiom => |a| {
                        formula = a.formula;
                        statement = .{ .id = stmt_id, .is_axiom = true };
                    },
                    .theorem => |t| {
                        // an accelerated premise poisons the certificate
                        if (!t.proven or t.accelerated.len != 0) return null;
                        formula = t.formula;
                        statement = .{ .id = stmt_id, .is_axiom = false };
                    },
                    .schema => return null,
                }
            }
            const node = self.pool.get(formula);
            const kind_ok = node == .eq or
                (node == .pred and symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2);
            if (!kind_ok) return null; // quantified or foreign hypotheses: accelerated path
            try premises.append(self.arena, .{
                .formula = formula,
                .step = step,
                .statement = statement,
                .rule_idx = undefined, // assigned below
                .elim = null,
            });
        }
        return self.arithCertCore(low, block_id, goal, premises.items, symbols, loc);
    }

    /// The planning and emission core shared by the surface certificate and
    /// the mixed-skeleton (D2) theory leaves.
    fn arithCertCore(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, premises: []CertPremise, symbols: presburger_mod.Symbols, loc: u32) ElabError!?kernel.Justification {
        var rules: std.ArrayList(simplify_mod.Rule) = .empty;
        for (wk_term_rule_names) |wk| {
            if (try self.wellKnownRule(wk, loc)) |r| try rules.append(self.arena, r);
        }
        if (rules.items.len == 0) return null;

        // hypothesis ground rules join the normalizing set
        for (premises) |*p| {
            const node = self.pool.get(p.formula);
            var rule: simplify_mod.Rule = undefined;
            if (node == .eq) {
                rule = .{
                    .source = .{ .step = .{ .id = @enumFromInt(0), .loc = loc } }, // patched at emission
                    .binders = &.{},
                    .lhs = node.eq.lhs,
                    .rhs = node.eq.rhs,
                    .formula = p.formula,
                };
            } else {
                // less_than(s0, t0): instantiate lessThanElim structurally
                const elim_fact = (try self.wellKnownFact("lessThanElim", loc)) orelse return null;
                const elim_rule = try self.strippedRule(elim_fact.formula, elim_fact.source);
                const elim_body = self.pool.get(elim_rule.lhs);
                if (elim_body != .bin or elim_body.bin.op != .implies) return null;
                const args = (try simplify_mod.matchRule(self.arena, self.pool, self.env, elim_rule, elim_body.bin.lhs, p.formula)) orelse return null;
                var implication = elim_rule.formula;
                for (args) |arg| {
                    const q = self.pool.get(implication);
                    if (q != .quant) return null;
                    implication = try self.pool.open(q.quant.body, arg);
                }
                const imp_node = self.pool.get(implication);
                if (imp_node != .bin or imp_node.bin.op != .implies) return null;
                const exists_formula = imp_node.bin.rhs;
                const ex_node = self.pool.get(exists_formula);
                if (ex_node != .quant or ex_node.quant.q != .exists) return null;
                const w: term.Node.Fvar = .{ .name = try self.freshNamed("w"), .sort = ex_node.quant.sort };
                const w_id = try self.pool.add(.{ .fvar = w });
                const opened_eq = try self.pool.open(ex_node.quant.body, w_id);
                const eq_node = self.pool.get(opened_eq);
                if (eq_node != .eq) return null;
                const sym_formula = try self.pool.add(.{ .eq = .{ .lhs = eq_node.eq.rhs, .rhs = eq_node.eq.lhs } });
                rule = .{
                    .source = .{ .step = .{ .id = @enumFromInt(0), .loc = loc } }, // patched at emission
                    .binders = &.{},
                    .lhs = eq_node.eq.rhs,
                    .rhs = eq_node.eq.lhs,
                    .formula = sym_formula,
                };
                p.elim = .{
                    .rule = elim_rule,
                    .args = args,
                    .implication = implication,
                    .exists_formula = exists_formula,
                    .w = w,
                    .opened_eq = opened_eq,
                    .sym_formula = sym_formula,
                };
            }
            // a self-embedding ground rule would loop the normalizer
            if (self.containsSubterm(rule.rhs, rule.lhs)) return null;
            p.rule_idx = rules.items.len;
            try rules.append(self.arena, rule);
        }
        const term_rule_count = rules.items.len;

        var comm_idx: ?usize = null;
        var swap_idx: ?usize = null;
        if (try self.wellKnownRule("addIsCommutative", loc)) |r| {
            comm_idx = rules.items.len;
            try rules.append(self.arena, r);
        }
        if (try self.wellKnownRule("addLeftSwap", loc)) |r| {
            swap_idx = rules.items.len;
            try rules.append(self.arena, r);
        }

        // peel the goal's universal prefix into synthesized fix blocks
        const u = try self.peelUniversal(goal, "arith");
        const opened = u.opened;
        const fix_vars = u.fix_vars;

        // plan completely before emitting anything (no rollback needed)
        const body = u.body;
        const body_node = self.pool.get(body);
        const plan: BodyPlan = plan: {
            if (try self.planInner(symbols, rules.items, term_rule_count, comm_idx, swap_idx, body, loc)) |inner| {
                break :plan .{ .inner = inner };
            }
            if (body_node == .quant and body_node.quant.q == .exists) {
                // C2c: search a constant witness tower, smallest first
                const zero_sym = symbols.zero orelse return null;
                const zero_term = try self.pool.addApp(.app, zero_sym, &.{});
                for (0..33) |k| {
                    const witness = (try self.buildTower(symbols, k, zero_term)) orelse return null;
                    const instance = try self.pool.open(body_node.quant.body, witness);
                    if (try self.planInner(symbols, rules.items, term_rule_count, comm_idx, swap_idx, instance, loc)) |inner| {
                        break :plan .{ .exists = .{ .witness = witness, .instance = instance, .inner = inner } };
                    }
                }
                return null;
            }
            return null;
        };

        var blocks: std.ArrayList(kernel.BlockId) = .empty;
        var parent = block_id;
        for (fix_vars) |fv| {
            const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .fix = fv });
            try blocks.append(self.arena, b);
            parent = b;
        }

        // hypothesis chains: citations, elim instances, witness unpacks;
        // each ground rule learns its source step here
        var unpacks: std.ArrayList(kernel.BlockId) = .empty;
        for (premises) |p| {
            const p_ref: kernel.SRef = p.step orelse blk: {
                const st = p.statement.?;
                break :blk try self.emitStep(low, parent, loc, p.formula, if (st.is_axiom)
                    .{ .axiom_ref = .{ .stmt = st.id, .loc = loc } }
                else
                    .{ .theorem_ref = .{ .stmt = st.id, .loc = loc } });
            };
            if (p.elim) |elim| {
                const imp_ref = try self.emitInstance(low, parent, loc, elim.rule, elim.args);
                const ex_ref = try self.emitStep(low, parent, loc, elim.exists_formula, .{ .modus_ponens = .{ .implication = imp_ref, .antecedent = p_ref } });
                const ub = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .unpack = .{ .v = elim.w, .source = ex_ref } });
                try unpacks.append(self.arena, ub);
                parent = ub;
                const eq_ref = try self.emitStep(low, ub, loc, elim.opened_eq, .{ .hypothesis = .{ .id = ub, .loc = loc } });
                const eq_node = self.pool.get(elim.opened_eq).eq;
                const refl_formula = try self.pool.add(.{ .eq = .{ .lhs = eq_node.lhs, .rhs = eq_node.lhs } });
                const refl_ref = try self.emitStep(low, ub, loc, refl_formula, .reflexivity);
                const sym_ref = try self.emitStep(low, ub, loc, elim.sym_formula, .{ .rewrite = .{ .equation = eq_ref, .target = refl_ref } });
                rules.items[p.rule_idx].source = .{ .step = sym_ref };
            } else {
                rules.items[p.rule_idx].source = .{ .step = p_ref };
            }
        }

        var carry: kernel.Justification = switch (plan) {
            .inner => |inner| try self.emitInner(low, parent, loc, inner),
            .exists => |ex| blk: {
                const inner_just = try self.emitInner(low, parent, loc, ex.inner);
                const inst_ref = try self.emitStep(low, parent, loc, ex.instance, inner_just);
                break :blk .{ .exists_intro = .{ .step = inst_ref, .witness = ex.witness, .witness_loc = loc } };
            },
        };
        // export the (witness-free) conclusion through each unpack
        var ui = unpacks.items.len;
        while (ui > 0) {
            ui -= 1;
            _ = try self.emitStep(low, unpacks.items[ui], loc, body, carry);
            self.closeBlock(low, unpacks.items[ui]);
            carry = .{ .exists_elim = .{ .id = unpacks.items[ui], .loc = loc } };
        }
        if (blocks.items.len == 0) return carry;
        _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, body, carry);
        var i = blocks.items.len;
        while (i > 1) {
            i -= 1;
            self.closeBlock(low, blocks.items[i]);
            _ = try self.emitStep(low, blocks.items[i - 1], loc, opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
        }
        self.closeBlock(low, blocks.items[0]);
        return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
    }

    // --- the `tautology` accelerated tactic: propositional consequence ------
    // The engine (src/smt.zig) decides; a `.valid` verdict becomes an
    // `.accelerated` kernel step the kernel accepts without a derivation. The
    // accelerated-tactic name marks the enclosing theorem accelerated; see
    // ACCELERATION.md.

    /// Record that the current proof leans on accelerated tactic `name`. By
    /// default this is a hard error — the goal must certify; the accelerated
    /// verdict is only accepted in `--fast` (verify.certify_arithmetic = false),
    /// where it marks the theorem accelerated.
    fn recordAccelerated(self: *Elaborator, name: StrId, loc: u32) ElabError!void {
        if (self.verify.certify_arithmetic) {
            return self.fail(loc, "'{s}' could not be emitted as kernel steps here; use --fast to accept the accelerated verdict", .{self.interner.str(name)});
        }
        for (self.accelerated_used.items) |o| {
            if (o == name) return;
        }
        try self.accelerated_used.append(self.arena, name);
    }

    /// `[by model(<Instance>) <source.theorem>]` — transfer a source theory's
    /// theorem to the goal through a declared model. Look up the model by the
    /// instance name (parsed into the `schema` slot), resolve the cited source
    /// theorem at its origin, `remapFormula` it through the model's interpretation
    /// (relativizing by the guard, if any), and check the result α-matches the
    /// goal. MVP: an ACCELERANT — `--fast` accepts the transfer wholesale (marks
    /// the theorem accelerated-by-`model`); default mode rejects (the strict
    /// obligation-discharge path is a later stage). See MODEL-DESIGN.md.
    fn modelJustification(self: *Elaborator, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const inst_tok = c.schema orelse
            return self.fail(loc, "model requires an instance: model(<Instance>) <source.theorem>", .{});
        if (c.refs.len != 1) {
            return self.fail(loc, "model(<Instance>) cites exactly one source theorem; got {d}", .{c.refs.len});
        }
        const inst_name = try self.internTok(inst_tok);
        const model = self.models.get(inst_name) orelse
            return self.fail(inst_tok.start, "unknown model '{s}'", .{self.text(inst_tok)});

        // resolve the cited source theorem at its origin and remap its formula.
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

        const name = self.interner.intern("model") catch return error.OutOfMemory;
        try self.recordAccelerated(name, loc);
        return .{ .accelerated = name };
    }

    /// The certifier chain's terminal: reached when every link declined a
    /// decided-valid goal. Under `--fast`, accept the accelerated verdict.
    /// Under the default, hard-error listing each link's decline reason (flat —
    /// the audience is an LLM, so every reason is equally machine-readable
    /// text), so a valid goal on a thin theory yields an actionable fix.
    /// `arithmetic ... fallback(<thm>)`: the certifier chain declined a valid
    /// goal, so cite the named theorem as the certificate. Elaborated — no
    /// accelerated step, no --fast — as long as <thm> is a proven theorem whose
    /// statement matches the goal. The kernel re-checks the match (a theorem_ref
    /// must equal the step claim); we also inherit <thm>'s own accelerated-tactic
    /// names, so a fallback onto an accelerated proof stays honestly accelerated.
    fn arithmeticFallback(self: *Elaborator, fb: lexer.Token, goal: TermId) ElabError!kernel.Justification {
        const stmt_id = self.env.findStatementId(self.file, try self.internTok(fb)) orelse
            return self.fail(fb.start, "fallback names unknown theorem '{s}'", .{self.text(fb)});
        const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
        switch (stmt) {
            .theorem => |t| {
                if (!t.proven) return self.fail(fb.start, "fallback theorem '{s}' is not proven", .{self.text(fb)});
                if (!self.pool.alphaEq(t.formula, goal)) {
                    return self.fail(fb.start, "fallback theorem '{s}' does not prove this goal", .{self.text(fb)});
                }
                try self.inheritAccelerated(t.accelerated);
                try self.inheritHoles(t.holes);
                return .{ .theorem_ref = .{ .stmt = stmt_id, .loc = fb.start } };
            },
            .axiom => return self.fail(fb.start, "fallback cites an axiom '{s}'; use a theorem", .{self.text(fb)}),
            .schema => return self.fail(fb.start, "fallback cites a schema '{s}'; use a theorem", .{self.text(fb)}),
        }
    }

    fn arithmeticTerminal(self: *Elaborator, loc: u32, reasons: []const Reason) ElabError!kernel.Justification {
        const accelerated_name = self.interner.intern("arithmetic") catch return error.OutOfMemory;
        if (!self.verify.certify_arithmetic) {
            // --fast: take the accelerated verdict, record it
            for (self.accelerated_used.items) |o| {
                if (o == accelerated_name) return .{ .accelerated = accelerated_name };
            }
            try self.accelerated_used.append(self.arena, accelerated_name);
            return .{ .accelerated = accelerated_name };
        }
        // default: hard error listing why each link declined
        var msg: std.Io.Writer.Allocating = .init(self.arena);
        msg.writer.writeAll("'arithmetic' is valid but no certifier could prove it here:") catch return error.OutOfMemory;
        for (certifiers, reasons) |link, reason| {
            const detail = switch (reason) {
                .out_of_scope => "form not in certification scope",
                .missing_symbol => |s| blk: {
                    var b: std.Io.Writer.Allocating = .init(self.arena);
                    b.writer.print("theory lacks symbol '{s}'", .{s}) catch return error.OutOfMemory;
                    break :blk b.written();
                },
                .missing_lemma => |s| blk: {
                    var b: std.Io.Writer.Allocating = .init(self.arena);
                    b.writer.print("theory lacks lemma '{s}'", .{s}) catch return error.OutOfMemory;
                    break :blk b.written();
                },
            };
            msg.writer.print("\n  - {s}: {s}", .{ link.name, detail }) catch return error.OutOfMemory;
        }
        msg.writer.writeAll("\nuse --fast to accept the accelerated verdict") catch return error.OutOfMemory;
        return self.fail(loc, "{s}", .{msg.written()});
    }

    /// Citing a fact inherits its accelerated-tactic names.
    fn inheritAccelerated(self: *Elaborator, names: []const StrId) Allocator.Error!void {
        outer: for (names) |name| {
            for (self.accelerated_used.items) |o| {
                if (o == name) continue :outer;
            }
            try self.accelerated_used.append(self.arena, name);
        }
    }

    /// Record hole dependence for the current theorem: `names` are the holes a
    /// cited fact rests on (a hole is [its own name]; a theorem is its `holes`).
    fn inheritHoles(self: *Elaborator, names: []const StrId) Allocator.Error!void {
        outer: for (names) |name| {
            for (self.holes_used.items) |o| {
                if (o == name) continue :outer;
            }
            try self.holes_used.append(self.arena, name);
        }
    }

    /// Resolve an accelerated tactic's premise refs to formulas (accessible step
    /// labels first, then statements); theorem citations inherit accelerated-tactic names.
    fn resolvePremises(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, c: ast.Step.Claim, comptime rule: []const u8) ElabError![]const TermId {
        const premises = try self.arena.alloc(TermId, c.refs.len);
        for (c.refs, premises) |ref, *out| {
            const name = try self.internTok(ref);
            if (low.labels.get(name)) |target| switch (target) {
                .step => |sid| {
                    const s = low.steps.items[@intFromEnum(sid)];
                    if (!lowAncestorOrSelf(low, s.block, block_id)) {
                        return self.fail(ref.start, "'{s}' is not accessible from this step (closed subproof)", .{self.text(ref)});
                    }
                    out.* = s.formula;
                },
                .block => return self.fail(ref.start, "'{s}' names a subproof; " ++ rule ++ " takes formulas", .{self.text(ref)}),
            } else {
                const stmt_id = try self.resolveStatementRef(ref);
                const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
                switch (stmt) {
                    .axiom => |a| out.* = a.formula,
                    .theorem => |t| {
                        if (!t.proven) return self.fail(ref.start, "cites unproven theorem '{s}'", .{self.text(ref)});
                        try self.inheritAccelerated(t.accelerated);
                        out.* = t.formula;
                    },
                    .schema => return self.fail(ref.start, "'{s}' is a schema; " ++ rule ++ " takes formulas", .{self.text(ref)}),
                }
            }
        }
        return premises;
    }

    // --- `ext` — the extensionality accelerated tactic ----------------------
    // Proves an equation LHS = RHS between extensional objects by reducing it,
    // through the theory's extensionality lemma, to a pointwise obligation, then
    // discharging that obligation by unfolding the operators (the theory's
    // characterization lemmas) and closing the residue (propositional →
    // `tautology`; equational → the equation certifier). A structure tactic,
    // model-parameterized: `ext(set)` / `ext(function)`. See ACCELERATION.md.

    /// A resolved extensionality model: the element sort, the extensionality
    /// lemma, and — read off the lemma's obligation — the characterization
    /// symbol (a `member`-style predicate, or an `apply`-style function).
    const ExtModel = struct {
        universe: term.SortId,
        lemma: TermId,
        lemma_source: simplify_mod.Source,
        /// each obligation is `forall x: <elementSort>; <body>`; count = 1 (function)
        /// or 2 (set, the two inclusions). Read from the lemma.
        obligation_count: usize,
    };

    fn extJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, quantified: bool) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const saved_theory = self.theory_file;
        defer self.theory_file = saved_theory;
        try self.enterTheory(c);

        // peel a forall prefix for the _quantified form.
        if (quantified) {
            const gn = self.pool.get(goal);
            if (gn != .quant or gn.quant.q != .forall) {
                return self.fail(loc, "ext_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
            }
            const u = try self.peelUniversal(goal, "ext");
            var blocks: std.ArrayList(kernel.BlockId) = .empty;
            var parent = block_id;
            for (u.fix_vars) |fv| {
                const b = try self.newBlock(low, try self.freshNamed("ext"), parent, .{ .fix = fv });
                try blocks.append(self.arena, b);
                parent = b;
            }
            const carry = try self.extEquation(low, parent, u.body, loc);
            if (blocks.items.len == 0) return carry;
            _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, u.body, carry);
            var i = blocks.items.len;
            while (i > 1) {
                i -= 1;
                self.closeBlock(low, blocks.items[i]);
                _ = try self.emitStep(low, blocks.items[i - 1], loc, u.opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
            }
            self.closeBlock(low, blocks.items[0]);
            return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
        }

        if (self.pool.get(goal) != .eq) {
            return self.fail(loc, "ext proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
        }
        return self.extEquation(low, block_id, goal, loc);
    }

    /// Prove a bare `LHS = RHS` by extensionality. Instantiate the ext lemma at
    /// (LHS, RHS), prove each pointwise obligation (fix x → unfold operators →
    /// close residue → forall_intro), then modus_ponens the chain to the
    /// equation. On any resolution failure, falls back to a located error.
    fn extEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, loc: u32) ElabError!kernel.Justification {
        const eq = self.pool.get(goal).eq;
        const model = (try self.extModel(loc)) orelse
            return self.fail(loc, "ext: no extensionality lemma (with an element-sort obligation) in scope", .{});

        // instantiate the ext lemma at (lhs, rhs): forall A, B; … peel two
        // binders with the goal's sides.
        var chain_ref = try self.emitStep(low, block_id, loc, model.lemma, sourceJust(model.lemma_source, loc));
        var chain_formula = model.lemma;
        for ([_]TermId{ eq.lhs, eq.rhs }) |arg| {
            const q = self.pool.get(chain_formula).quant;
            chain_formula = try self.pool.open(q.body, arg);
            chain_ref = try self.emitStep(low, block_id, loc, chain_formula, .{ .forall_elim = .{ .step = chain_ref, .with = arg, .with_loc = loc } });
        }
        // chain_formula is now `Ob1 -> (Ob2 ->) lhs = rhs`. Prove each Obi and
        // modus_ponens; the LAST modus_ponens (proving `lhs = rhs` = the goal)
        // is this tactic's returned justification, not an emitted step.
        for (0..model.obligation_count) |i| {
            const imp = self.pool.get(chain_formula).bin;
            const ob = imp.lhs; // forall x: <elementSort>; body
            const ob_ref = try self.extObligation(low, block_id, ob, model, loc);
            const mp: kernel.Justification = .{ .modus_ponens = .{ .implication = chain_ref, .antecedent = ob_ref } };
            chain_formula = imp.rhs;
            if (i + 1 == model.obligation_count) return mp; // proves the goal
            chain_ref = try self.emitStep(low, block_id, loc, chain_formula, mp);
        }
        // obligation_count == 0: the lemma had no premises (degenerate) — the
        // instantiated chain IS the equation; re-cite it. Unreachable for the
        // set/function models, but keep it total.
        return .{ .forall_elim = .{ .step = chain_ref, .with = eq.rhs, .with_loc = loc } };
    }

    /// Build the axiom/theorem citation justification for a lemma `Source`
    /// resolved via wellKnownFact (which only yields axiom/theorem sources).
    fn sourceJust(source: simplify_mod.Source, loc: u32) kernel.Justification {
        return switch (source) {
            .axiom => |a| .{ .axiom_ref = .{ .stmt = a.id, .loc = loc } },
            .theorem => |t| .{ .theorem_ref = .{ .stmt = t.id, .loc = loc } },
            .step => unreachable, // wellKnownFact never returns a step source
        };
    }

    /// Prove one obligation `forall x: <elementSort>; body`. `fix x`, unfold every
    /// operator characterization lemma relevant to `body`, close the residue,
    /// forall_intro. Returns the step proving the obligation.
    fn extObligation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, ob: TermId, model: ExtModel, loc: u32) ElabError!kernel.SRef {
        const q = self.pool.get(ob).quant; // forall x: <elementSort>; body
        const x: term.Node.Fvar = .{ .name = try self.freshNamed("x"), .sort = model.universe };
        const x_id = try self.pool.add(.{ .fvar = x });
        const body = try self.pool.open(q.body, x_id);
        const fix_b = try self.newBlock(low, try self.freshNamed("ext-element"), block_id, .{ .fix = x });

        // close the residue, dispatching on its shape:
        //   equation  `apply(f,x) = apply(g,x)`  — FUNCTION model: rewrite by the
        //     operator `<op>Apply` lemmas and join (the equation certifier).
        //   otherwise `member(x,·) -> member(x,·)` — SET model: unfold membership
        //     via `<op>Member` lemmas and close propositionally with tautology.
        const residue = if (self.pool.get(body) == .eq)
            try self.extFunctionResidue(low, fix_b, body, loc)
        else blk: {
            var premises: std.ArrayList(TautCert.Premise) = .empty;
            try self.extUnfold(low, fix_b, body, x_id, &premises, loc);
            const steps_mark = low.steps.items.len;
            const blocks_mark = low.blocks.items.len;
            break :blk (try self.emitTautologyFrom(low, fix_b, body, premises.items, loc, steps_mark, blocks_mark)) orelse
                return self.fail(loc, "ext: could not close the pointwise obligation propositionally (is the identity true?)", .{});
        };
        _ = try self.emitStep(low, fix_b, loc, body, residue);
        self.closeBlock(low, fix_b);
        return try self.emitStep(low, block_id, loc, ob, .{ .forall_intro = .{ .id = fix_b, .loc = loc } });
    }

    /// Close a function-model pointwise obligation `apply(f,x) = apply(g,x)`:
    /// gather the operator `<op>Apply` rewrite lemmas for every `apply(op(...),x)`
    /// on either side, normalize both sides, and emit the rewrite join.
    fn extFunctionResidue(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, eq_goal: TermId, loc: u32) ElabError!kernel.Justification {
        const eq = self.pool.get(eq_goal).eq;
        if (self.pool.alphaEq(eq.lhs, eq.rhs)) return .reflexivity;
        // collect every apply-characterization lemma in the theory scope: any
        // axiom/theorem whose stripped LHS is `apply(…, …)`. Enumerating the
        // scope (rather than guessing `<op>Apply` names) handles const heads
        // like `identityFn` (whose lemma is `identityApply`, not `identityFnApply`).
        const rules = try self.extApplyLemmas(loc);
        if (rules.len == 0) {
            return self.fail(loc, "ext: no apply lemmas in scope to unfold '{s}'", .{try self.renderTerm(eq_goal)});
        }
        const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules, eq.lhs, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "ext: rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules, eq.rhs, 1000) catch |e| switch (e) {
            error.Limit => return self.fail(loc, "ext: rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        if (!self.pool.alphaEq(rs.nf, rt.nf)) {
            return self.fail(loc, "ext: pointwise values differ: '{s}' vs '{s}' (is the identity true?)", .{
                try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
            });
        }
        return self.emitJoin(low, block_id, loc, rules, eq.lhs, eq.rhs, rs, rt);
    }

    /// Every apply-characterization rewrite lemma in the current theory scope:
    /// each axiom/theorem whose stripped LHS is `apply(…, …)` (`composeApply`,
    /// `identityApply`, …), turned into a rewrite rule. Enumerates the scope so a
    /// const head (`identityFn`) is handled without name-guessing.
    fn extApplyLemmas(self: *Elaborator, loc: u32) ElabError![]const simplify_mod.Rule {
        const apply_sym = (try self.wellKnownSym("apply")) orelse return &.{};
        var rules: std.ArrayList(simplify_mod.Rule) = .empty;
        for (self.env.scopeStatements(self.theoryScope())) |sid| {
            const stmt = self.env.statements.items[@intFromEnum(sid)];
            const fact: struct { formula: TermId, source: simplify_mod.Source } = switch (stmt) {
                .axiom => |a| .{ .formula = a.formula, .source = .{ .axiom = .{ .id = sid, .loc = loc } } },
                .theorem => |t| if (t.proven and t.accelerated.len == 0)
                    .{ .formula = t.formula, .source = .{ .theorem = .{ .id = sid, .loc = loc } } }
                else
                    continue,
                .schema => continue,
            };
            // strip the forall prefix; keep only equations whose lhs is apply(…).
            var body = fact.formula;
            while (self.pool.get(body) == .quant and self.pool.get(body).quant.q == .forall) {
                const qn = self.pool.get(body).quant;
                const fv = try self.pool.add(.{ .fvar = .{ .name = try self.freshNamed("p"), .sort = qn.sort } });
                body = try self.pool.open(qn.body, fv);
            }
            const bn = self.pool.get(body);
            if (bn != .eq) continue;
            const lhs = self.pool.get(bn.eq.lhs);
            if (lhs != .app or lhs.app.sym != apply_sym) continue;
            switch (try self.equationRule(fact.formula, fact.source)) {
                .rule => |r| try rules.append(self.arena, r),
                else => {},
            }
        }
        return rules.items;
    }

    /// For each `member(x, op(a,b,…))` subterm in `formula`, instantiate the
    /// operator's characterization lemma `<op>Member` at (a, b, …, x) and emit
    /// it as a premise. Recurses structurally.
    fn extUnfold(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, formula: TermId, x_id: TermId, out: *std.ArrayList(TautCert.Premise), loc: u32) ElabError!void {
        const node = self.pool.get(formula);
        switch (node) {
            .pred => |p| {
                // member(x, s): if s = op(args…), unfold via <op>Member.
                const args = self.pool.args(p);
                if (args.len == 2) {
                    const s = args[1];
                    const sn = self.pool.get(s);
                    if (sn == .app) {
                        try self.extUnfoldOp(low, block_id, sn.app, x_id, out, loc);
                    }
                }
            },
            .bin => |b| {
                try self.extUnfold(low, block_id, b.lhs, x_id, out, loc);
                try self.extUnfold(low, block_id, b.rhs, x_id, out, loc);
            },
            .not => |inner| try self.extUnfold(low, block_id, inner, x_id, out, loc),
            else => {},
        }
    }

    /// Unfold one operator application `op(a, b, …)` appearing as a set: emit
    /// `<op>Member` instantiated at (a, b, …, x). Dedups by formula.
    fn extUnfoldOp(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, app: term.Node.App, x_id: TermId, out: *std.ArrayList(TautCert.Premise), loc: u32) ElabError!void {
        const op_name = self.env.sym(app.sym).name;
        const lemma_name = try std.fmt.allocPrint(self.arena, "{s}Member", .{self.interner.str(op_name)});
        const fact = (try self.wellKnownFact(lemma_name, loc)) orelse return; // no lemma: leave atom opaque
        // instantiate: the lemma is `forall <setargs>; forall x; <iff>`.
        // bind the operator's args, then x.
        var ref = try self.emitStep(low, block_id, loc, fact.formula, sourceJust(fact.source, loc));
        var cur = fact.formula;
        // COPY the arg ids: pool.args aliases pool.extra, which the emitStep/
        // pool.open calls below grow — the slice would dangle (0xAAAAAAAA).
        const op_args = try self.arena.dupe(TermId, self.pool.args(app));
        for (op_args) |a| {
            const qn = self.pool.get(cur);
            if (qn != .quant) return;
            cur = try self.pool.open(qn.quant.body, a);
            ref = try self.emitStep(low, block_id, loc, cur, .{ .forall_elim = .{ .step = ref, .with = a, .with_loc = loc } });
        }
        // now bind x
        const qn = self.pool.get(cur);
        if (qn != .quant) return;
        cur = try self.pool.open(qn.quant.body, x_id);
        ref = try self.emitStep(low, block_id, loc, cur, .{ .forall_elim = .{ .step = ref, .with = x_id, .with_loc = loc } });
        // dedup
        for (out.items) |p| if (self.pool.alphaEq(p.formula, cur)) return;
        try out.append(self.arena, .{ .formula = cur, .ref = ref });
        // recurse into the operator's set arguments (nested operators unfold too)
        for (op_args) |a| {
            const an = self.pool.get(a);
            if (an == .app) try self.extUnfoldOp(low, block_id, an.app, x_id, out, loc);
        }
    }

    /// Resolve the extensionality model in the current theory scope. Tries
    /// `extensionality` then `funcExtensionality`; reads the element sort +
    /// obligation count from the lemma's shape. The element sort is derived
    /// STRUCTURALLY from the first obligation's binder (`forall x: <sort>; …`),
    /// not looked up by name — so the tactic works whatever that sort is called
    /// (`Element`, `Universe`, …).
    fn extModel(self: *Elaborator, loc: u32) ElabError!?ExtModel {
        const fact = (try self.wellKnownFact("extensionality", loc)) orelse
            (try self.wellKnownFact("funcExtensionality", loc)) orelse return null;
        // count the leading obligations: peel `forall A, B;` then count the
        // `(forall x; …) ->` premises before the `A = B` conclusion.
        var body = fact.formula;
        var peeled: usize = 0;
        while (self.pool.get(body) == .quant and self.pool.get(body).quant.q == .forall and peeled < 2) : (peeled += 1) {
            const fv = try self.pool.add(.{ .fvar = .{ .name = try self.freshNamed("s"), .sort = self.pool.get(body).quant.sort } });
            body = try self.pool.open(self.pool.get(body).quant.body, fv);
        }
        // the element sort is the binder sort of the first obligation
        // `forall x: <elementSort>; …` (lhs of the first implication).
        var universe: ?term.SortId = null;
        var obligations: usize = 0;
        while (self.pool.get(body) == .bin and self.pool.get(body).bin.op == .implies) : (obligations += 1) {
            const premise = self.pool.get(body).bin.lhs;
            if (universe == null and self.pool.get(premise) == .quant) {
                universe = self.pool.get(premise).quant.sort;
            }
            body = self.pool.get(body).bin.rhs;
        }
        return .{ .universe = universe orelse return null, .lemma = fact.formula, .lemma_source = fact.source, .obligation_count = obligations };
    }

    fn tautologyJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const premises = try self.resolvePremises(low, block_id, c, "tautology");
        const verdict = smt_mod.tautology(self.arena, self.pool, premises, goal) catch return error.OutOfMemory;
        switch (verdict) {
            .valid => {
                // certificate first: replay the truth search as ordinary
                // kernel steps — kernel-checked, no accelerated step
                if (try self.tautologyCertificate(low, block_id, goal, c)) |just| {
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

    /// Prove `goal` propositionally from already-emitted premise steps (each a
    /// `{formula, ref}`), replaying the truth search as kernel steps. Returns
    /// null (rolling back to the marks) when the step budget runs out. Shared by
    /// the surface `tautology` cert and any tactic that synthesizes premises
    /// then wants a propositional close (e.g. `ext`'s set residue).
    fn emitTautologyFrom(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, premise_steps: []const TautCert.Premise, loc: u32, steps_mark: usize, blocks_mark: usize) ElabError!?kernel.Justification {
        var atoms: std.ArrayList(TermId) = .empty;
        for (premise_steps) |p| try smt_mod.collectAtoms(self.arena, self.pool, &atoms, p.formula);
        try smt_mod.collectAtoms(self.arena, self.pool, &atoms, goal);

        const assignment = try self.arena.alloc(?bool, atoms.items.len);
        @memset(assignment, null);
        const lits = try self.arena.alloc(?TautCert.Lit, atoms.items.len);
        @memset(lits, null);
        var cert: TautCert = .{
            .elab = self,
            .low = low,
            .loc = loc,
            .goal = goal,
            .premises = premise_steps,
            .atoms = atoms.items,
            .assignment = assignment,
            .lits = lits,
        };
        const just = cert.goalJust(block_id) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return error.Recover,
            error.Budget => {
                low.steps.shrinkRetainingCapacity(steps_mark);
                low.blocks.shrinkRetainingCapacity(blocks_mark);
                return null;
            },
        };
        return just;
    }

    const TautCert = struct {
        elab: *Elaborator,
        low: *Lowering,
        loc: u32,
        goal: TermId,
        premises: []const Premise,
        atoms: []const TermId,
        assignment: []?bool,
        /// per atom: the assume block whose hypothesis is the literal
        lits: []?Lit,
        budget: usize = 2000,
        /// D2: with the arithmetic vocabulary present, a branch whose goal
        /// is boolean-false may still close by deriving a false-assigned
        /// theory atom from the true-assigned literals (absurd)
        symbols: ?presburger_mod.Symbols = null,

        const Premise = struct { formula: TermId, ref: kernel.SRef };
        const Lit = struct { block: kernel.BlockId, positive: bool };
        const CertError = error{ Budget, Recover, OutOfMemory };

        fn emit(self: *TautCert, block: kernel.BlockId, formula: TermId, just: kernel.Justification) CertError!kernel.SRef {
            if (self.budget == 0) return error.Budget;
            self.budget -= 1;
            return self.elab.emitStep(self.low, block, self.loc, formula, just);
        }

        fn openAssume(self: *TautCert, parent: kernel.BlockId, formula: TermId) CertError!kernel.BlockId {
            return self.elab.newBlock(self.low, try self.elab.freshNamed("tautology"), parent, .{ .assume = formula });
        }

        fn bref(self: *const TautCert, block: kernel.BlockId) kernel.BRef {
            return .{ .id = block, .loc = self.loc };
        }

        fn eval(self: *const TautCert, f: TermId) ?bool {
            return smt_mod.eval(self.elab.pool, self.atoms, self.assignment, f);
        }

        fn litOf(self: *const TautCert, f: TermId) Lit {
            for (self.atoms, self.lits) |a, lit| {
                if (self.elab.pool.alphaEq(a, f)) return lit.?; // assigned, or eval could not have decided
            }
            unreachable; // every leaf is a collected atom
        }

        /// Justification for a step claiming the goal in `block` (the step
        /// itself is not emitted — the caller owns the claim).
        fn goalJust(self: *TautCert, block: kernel.BlockId) CertError!kernel.Justification {
            for (self.premises) |p| {
                if (self.eval(p.formula) == false) {
                    const refuted = try self.deriveFalse(block, p.formula);
                    return .{ .absurd = .{ .s1 = p.ref, .s2 = refuted } };
                }
            }
            if (self.eval(self.goal) == true) {
                return self.trueJust(block, self.goal);
            }
            if (self.eval(self.goal) == false) {
                // boolean dead end: only a theory conflict can close it
                if (try self.theoryLeaf(block)) |just| return just;
                if (std.mem.indexOfScalar(?bool, self.assignment, null) == null) {
                    return error.Budget; // fully assigned and underivable
                }
                // more literals may make the conflict derivable: keep splitting
            }
            // split on the first unassigned atom with an inline excluded
            // middle and recurse into both branches
            const idx = for (self.assignment, 0..) |v, i| {
                if (v == null) break i;
            } else unreachable; // an unassigned atom exists here
            const atom = self.atoms[idx];
            const not_atom = try self.pool().add(.{ .not = atom });
            const disj = try self.pool().add(.{ .bin = .{ .op = .or_op, .lhs = atom, .rhs = not_atom } });
            const lem = try self.emitLem(block, atom, not_atom, disj);

            const left = try self.openAssume(block, atom);
            self.assignment[idx] = true;
            self.lits[idx] = .{ .block = left, .positive = true };
            const left_just = try self.goalJust(left);
            _ = try self.emit(left, self.goal, left_just);
            self.elab.closeBlock(self.low, left);

            const right = try self.openAssume(block, not_atom);
            self.assignment[idx] = false;
            self.lits[idx] = .{ .block = right, .positive = false };
            const right_just = try self.goalJust(right);
            _ = try self.emit(right, self.goal, right_just);
            self.elab.closeBlock(self.low, right);

            self.assignment[idx] = null;
            self.lits[idx] = null;
            return .{ .or_elim = .{ .disj = lem, .left = self.bref(left), .right = self.bref(right) } };
        }

        fn pool(self: *const TautCert) *term.Pool {
            return self.elab.pool;
        }

        /// Is this atom usable by the arithmetic certificate core?
        fn arithAtom(self: *const TautCert, atom: TermId) bool {
            const symbols = self.symbols orelse return false;
            const node = self.pool().get(atom);
            return node == .eq or
                (node == .pred and symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2);
        }

        /// D2 leaf: derive some false-assigned theory atom from the
        /// true-assigned literals, then explode it against its assumption.
        fn theoryLeaf(self: *TautCert, block: kernel.BlockId) CertError!?kernel.Justification {
            const symbols = self.symbols orelse return null;
            // the true-assigned arithmetic literals, restated as steps
            var cert_premises: std.ArrayList(CertPremise) = .empty;
            for (self.atoms, self.assignment, self.lits) |atom, value, lit| {
                if (value != true or !self.arithAtom(atom)) continue;
                const ref = try self.emit(block, atom, .{ .hypothesis = self.bref(lit.?.block) });
                try cert_premises.append(self.elab.arena, .{
                    .formula = atom,
                    .step = ref,
                    .statement = null,
                    .rule_idx = undefined,
                    .elim = null,
                });
            }
            // rule premises that hold on this branch participate too
            for (self.premises) |p| {
                if (self.eval(p.formula) != true or !self.arithAtom(p.formula)) continue;
                try cert_premises.append(self.elab.arena, .{
                    .formula = p.formula,
                    .step = p.ref,
                    .statement = null,
                    .rule_idx = undefined,
                    .elim = null,
                });
            }
            for (self.atoms, self.assignment, 0..) |atom, value, idx| {
                if (value != false or !self.arithAtom(atom)) continue;
                const just = (try self.elab.arithCertCore(self.low, block, atom, cert_premises.items, symbols, self.loc)) orelse continue;
                const derived = try self.emit(block, atom, just);
                const not_atom = try self.pool().add(.{ .not = atom });
                const refuted = try self.emit(block, not_atom, .{ .hypothesis = self.bref(self.lits[idx].?.block) });
                return .{ .absurd = .{ .s1 = derived, .s2 = refuted } };
            }
            return null;
        }

        /// atom or not atom, the classical way: not_intro on the negated
        /// disjunction, then double_negation
        fn emitLem(self: *TautCert, block: kernel.BlockId, atom: TermId, not_atom: TermId, disj: TermId) CertError!kernel.SRef {
            const not_disj = try self.pool().add(.{ .not = disj });
            const outer = try self.openAssume(block, not_disj);
            const hyp_outer = try self.emit(outer, not_disj, .{ .hypothesis = self.bref(outer) });
            const inner = try self.openAssume(outer, atom);
            const hyp_inner = try self.emit(inner, atom, .{ .hypothesis = self.bref(inner) });
            const or_left = try self.emit(inner, disj, .{ .or_intro_left = hyp_inner });
            self.elab.closeBlock(self.low, inner);
            const derived_not = try self.emit(outer, not_atom, .{ .not_intro = .{ .block = self.bref(inner), .s1 = or_left, .s2 = hyp_outer } });
            const or_right = try self.emit(outer, disj, .{ .or_intro_right = derived_not });
            self.elab.closeBlock(self.low, outer);
            const not_not = try self.pool().add(.{ .not = not_disj });
            const nn = try self.emit(block, not_not, .{ .not_intro = .{ .block = self.bref(outer), .s1 = or_right, .s2 = hyp_outer } });
            return self.emit(block, disj, .{ .double_negation = nn });
        }

        /// Emit a step proving `f` (which evaluates true) in `block`.
        fn deriveTrue(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.SRef {
            const just = try self.trueJust(block, f);
            return self.emit(block, f, just);
        }

        fn trueJust(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.Justification {
            switch (self.pool().get(f)) {
                .bin => |b| switch (b.op) {
                    .and_op => return .{ .and_intro = .{
                        .left = try self.deriveTrue(block, b.lhs),
                        .right = try self.deriveTrue(block, b.rhs),
                    } },
                    .or_op => {
                        if (self.eval(b.lhs) == true) {
                            return .{ .or_intro_left = try self.deriveTrue(block, b.lhs) };
                        }
                        return .{ .or_intro_right = try self.deriveTrue(block, b.rhs) };
                    },
                    .implies => {
                        const blk = try self.openAssume(block, b.lhs);
                        if (self.eval(b.rhs) == true) {
                            _ = try self.deriveTrue(blk, b.rhs);
                        } else {
                            // the antecedent is false: assume it and explode
                            const hyp = try self.emit(blk, b.lhs, .{ .hypothesis = self.bref(blk) });
                            const refuted = try self.deriveFalse(blk, b.lhs);
                            _ = try self.emit(blk, b.rhs, .{ .absurd = .{ .s1 = hyp, .s2 = refuted } });
                        }
                        self.elab.closeBlock(self.low, blk);
                        return .{ .implies_intro = self.bref(blk) };
                    },
                },
                // f = not inner, true: exactly a proof that inner is false
                .not => |inner| return self.falseJust(block, inner),
                // an atom assigned true: restate its assumption
                else => return .{ .hypothesis = self.bref(self.litOf(f).block) },
            }
        }

        /// Emit a step proving `not f` (f evaluates false) in `block`.
        fn deriveFalse(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.SRef {
            const just = try self.falseJust(block, f);
            const nf = try self.pool().add(.{ .not = f });
            return self.emit(block, nf, just);
        }

        fn falseJust(self: *TautCert, block: kernel.BlockId, f: TermId) CertError!kernel.Justification {
            switch (self.pool().get(f)) {
                .bin => |b| switch (b.op) {
                    .and_op => {
                        // a false conjunct refutes the conjunction
                        const left_false = self.eval(b.lhs) == false;
                        const side = if (left_false) b.lhs else b.rhs;
                        const refuted = try self.deriveFalse(block, side);
                        const blk = try self.openAssume(block, f);
                        const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                        const elim = try self.emit(blk, side, if (left_false)
                            .{ .and_elim_left = hyp }
                        else
                            .{ .and_elim_right = hyp });
                        self.elab.closeBlock(self.low, blk);
                        return .{ .not_intro = .{ .block = self.bref(blk), .s1 = elim, .s2 = refuted } };
                    },
                    .or_op => {
                        // both disjuncts are false; case-split to reproduce
                        // the left one, contradicting its refutation
                        const not_left = try self.deriveFalse(block, b.lhs);
                        const not_right = try self.deriveFalse(block, b.rhs);
                        const blk = try self.openAssume(block, f);
                        const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                        const left = try self.openAssume(blk, b.lhs);
                        _ = try self.emit(left, b.lhs, .{ .hypothesis = self.bref(left) });
                        self.elab.closeBlock(self.low, left);
                        const right = try self.openAssume(blk, b.rhs);
                        const rh = try self.emit(right, b.rhs, .{ .hypothesis = self.bref(right) });
                        _ = try self.emit(right, b.lhs, .{ .absurd = .{ .s1 = rh, .s2 = not_right } });
                        self.elab.closeBlock(self.low, right);
                        const conc = try self.emit(blk, b.lhs, .{ .or_elim = .{ .disj = hyp, .left = self.bref(left), .right = self.bref(right) } });
                        self.elab.closeBlock(self.low, blk);
                        return .{ .not_intro = .{ .block = self.bref(blk), .s1 = conc, .s2 = not_left } };
                    },
                    .implies => {
                        // true antecedent, false consequent
                        const ante = try self.deriveTrue(block, b.lhs);
                        const not_conseq = try self.deriveFalse(block, b.rhs);
                        const blk = try self.openAssume(block, f);
                        const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                        const conseq = try self.emit(blk, b.rhs, .{ .modus_ponens = .{ .implication = hyp, .antecedent = ante } });
                        self.elab.closeBlock(self.low, blk);
                        return .{ .not_intro = .{ .block = self.bref(blk), .s1 = conseq, .s2 = not_conseq } };
                    },
                },
                .not => |inner| {
                    // not f = not not inner, with inner true
                    const truth = try self.deriveTrue(block, inner);
                    const blk = try self.openAssume(block, f);
                    const hyp = try self.emit(blk, f, .{ .hypothesis = self.bref(blk) });
                    self.elab.closeBlock(self.low, blk);
                    return .{ .not_intro = .{ .block = self.bref(blk), .s1 = truth, .s2 = hyp } };
                },
                // an atom assigned false: its assumption IS the negation
                else => return .{ .hypothesis = self.bref(self.litOf(f).block) },
            }
        }
    };

    /// D2: a mixed goal (opaque + arithmetic atoms) replays as a
    /// tautology-style skeleton certificate whose boolean dead ends close
    /// via the arithmetic certificate core (theoryLeaf). Elaborated; an
    /// underivable leaf or exhausted budget rolls back to the accelerated path.
    fn arithMixedCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols) ElabError!?kernel.Justification {
        const loc = c.rule.start;
        const steps_mark = low.steps.items.len;
        const blocks_mark = low.blocks.items.len;

        // premise steps (label refs are steps; statements get citations)
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
                switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
                    .axiom => |a| out.* = .{
                        .formula = a.formula,
                        .ref = try self.emitStep(low, block_id, loc, a.formula, .{ .axiom_ref = .{ .stmt = stmt_id, .loc = loc } }),
                    },
                    .theorem => |t| {
                        if (!t.proven or t.accelerated.len != 0) {
                            low.steps.shrinkRetainingCapacity(steps_mark);
                            low.blocks.shrinkRetainingCapacity(blocks_mark);
                            return null; // an accelerated premise poisons the certificate
                        }
                        out.* = .{
                            .formula = t.formula,
                            .ref = try self.emitStep(low, block_id, loc, t.formula, .{ .theorem_ref = .{ .stmt = stmt_id, .loc = loc } }),
                        };
                    },
                    .schema => unreachable, // resolvePremises rejected these
                }
            }
        }

        // peel the universal prefix
        const u = try self.peelUniversal(goal, "arith");
        const opened = u.opened;
        const fix_vars = u.fix_vars;
        const body = u.body;

        var atoms: std.ArrayList(TermId) = .empty;
        for (premise_steps) |p| try smt_mod.collectAtoms(self.arena, self.pool, &atoms, p.formula);
        try smt_mod.collectAtoms(self.arena, self.pool, &atoms, body);
        if (atoms.items.len > smt_mod.atom_limit) {
            low.steps.shrinkRetainingCapacity(steps_mark);
            low.blocks.shrinkRetainingCapacity(blocks_mark);
            return null;
        }
        const assignment = try self.arena.alloc(?bool, atoms.items.len);
        @memset(assignment, null);
        const lits = try self.arena.alloc(?TautCert.Lit, atoms.items.len);
        @memset(lits, null);

        var blocks: std.ArrayList(kernel.BlockId) = .empty;
        var parent = block_id;
        for (fix_vars) |fv| {
            const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .fix = fv });
            try blocks.append(self.arena, b);
            parent = b;
        }

        var cert: TautCert = .{
            .elab = self,
            .low = low,
            .loc = loc,
            .goal = body,
            .premises = premise_steps,
            .atoms = atoms.items,
            .assignment = assignment,
            .lits = lits,
            .symbols = symbols,
        };
        const body_just = cert.goalJust(parent) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return error.Recover,
            error.Budget => {
                low.steps.shrinkRetainingCapacity(steps_mark);
                low.blocks.shrinkRetainingCapacity(blocks_mark);
                return null;
            },
        };
        if (blocks.items.len == 0) return body_just;
        _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, body, body_just);
        var i = blocks.items.len;
        while (i > 1) {
            i -= 1;
            self.closeBlock(low, blocks.items[i]);
            _ = try self.emitStep(low, blocks.items[i - 1], loc, opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
        }
        self.closeBlock(low, blocks.items[0]);
        return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
    }

    // --- the `arithmetic` accelerated tactic: Presburger arithmetic over Nat -
    // The engine (src/presburger.zig) decides by quantifier elimination; a
    // `.valid` verdict becomes an `.accelerated` kernel step. See ACCELERATION.md.

    /// The arithmetic vocabulary, resolved by well-known name in this file's
    /// scope. Absent names shrink the fragment.
    /// Is `atom` a relation the arithmetic fragment is meant to decide — an
    /// equation/disequation, or a `less_than` — as opposed to a genuinely
    /// foreign predicate (which is legitimately opaque)?
    fn looksArithmeticRelation(self: *const Elaborator, atom: TermId, symbols: presburger_mod.Symbols) bool {
        return switch (self.pool.get(atom)) {
            .eq => true,
            .not => |inner| self.pool.get(inner) == .eq,
            .pred => |p| symIs(p.sym, symbols.less_than),
            else => false,
        };
    }

    fn arithmeticSymbols(self: *Elaborator) ElabError!presburger_mod.Symbols {
        var symbols: presburger_mod.Symbols = .{};
        symbols.zero = try self.wellKnownSym("ZERO");
        symbols.one = try self.wellKnownSym("ONE");
        symbols.succ = try self.wellKnownSym("succ");
        symbols.add = try self.wellKnownSym("add");
        symbols.mul = try self.wellKnownSym("mul");
        symbols.less_than = try self.wellKnownSym("less_than");
        const anchor = symbols.succ orelse symbols.add orelse symbols.zero orelse symbols.one;
        if (anchor) |sym| symbols.nat = self.env.sym(sym).result;
        return symbols;
    }

    fn wellKnownSym(self: *Elaborator, name: []const u8) ElabError!?term.SymId {
        const id = self.interner.intern(name) catch return error.OutOfMemory;
        return self.env.findSym(self.theoryScope(), id);
    }

    /// A less_than(lo, hi) atom peeled from the goal, with the step that makes
    /// it available inside the proof.
    const OrderHyp = struct { lo: TermId, hi: TermId, ref: kernel.SRef };

    /// Why a certifier link declined a decided-valid goal. Surfaced (flat) at
    /// the honest terminal when every link declines, so a goal that is valid
    /// but sits on a thin theory yields an actionable fix rather than "write a
    /// manual proof". `out_of_scope` is the expected "not my shape"; the
    /// `missing_*` variants name a gap in the theory the user can close.
    const Reason = union(enum) {
        out_of_scope,
        missing_symbol: []const u8,
        missing_lemma: []const u8,
    };

    /// A certifier link's result: it either emits kernel steps (certified) or
    /// declines with a reason. Errors (OOM/Recover) stay in ElabError.
    const Outcome = union(enum) {
        certified: kernel.Justification,
        declined: Reason,
    };

    /// One named entry in the certifier chain: the link's display name (for the
    /// terminal reason list) and a function producing its Outcome.
    const Certifier = struct {
        name: []const u8,
        run: *const fn (*Elaborator, *Lowering, kernel.BlockId, TermId, ast.Step.Claim, presburger_mod.Symbols, u32) ElabError!Outcome,
    };

    /// The certifier chain, walked first-`certified`-wins. Each link's decline
    /// reason is collected for the honest terminal. A future Cooper-QE-replay
    /// and a user-driven `manual` link slot in here as peer entries.
    const certifiers = [_]Certifier{
        .{ .name = "equation/order/exists", .run = &equationCertifier },
        .{ .name = "mixed-skeleton", .run = &mixedCertifier },
        .{ .name = "farkas", .run = &farkasCertificate },
        .{ .name = "cooper", .run = &cooperCertificate },
    };

    /// Adapter: the equation/order/exists cert returns ?Justification; a null
    /// is an "out of scope" decline (its internals resolve their own lemmas).
    fn equationCertifier(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
        _ = loc;
        if (try self.arithmeticCertificate(low, block_id, goal, c, symbols)) |just| return .{ .certified = just };
        return .{ .declined = .out_of_scope };
    }

    /// Adapter: the mixed-skeleton (D2) cert returns ?Justification.
    fn mixedCertifier(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
        _ = loc;
        if (try self.arithMixedCertificate(low, block_id, goal, c, symbols)) |just| return .{ .certified = just };
        return .{ .declined = .out_of_scope };
    }

    /// The Farkas certifier link over the difference-logic fragment. A goal
    /// `forall v..; H1 -> ... -> Hn -> C` whose Hi are strict-order atoms is
    /// certified by composing them with `lessThanTransitive`. Three conclusion
    /// shapes (see emitFarkasConclusion): order composition `less_than(s, t)`
    /// (fold a path s < ... < t), the self-loop `less_than(x, x)` (fold a
    /// cycle), and INFEASIBILITY of an arbitrary conclusion (fold a cycle to
    /// `less_than(x, x)`, contradict with `lessThanIrreflexive`, `absurd`).
    /// Combines SEVERAL hypotheses, which the single-atom order cert cannot.
    /// Declines when the goal is not this shape or a needed order lemma is
    /// absent in the theory scope.
    fn farkasCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
        _ = c;
        const less_than = symbols.less_than orelse return .{ .declined = .{ .missing_symbol = "less_than" } };
        const nat = symbols.nat orelse return .{ .declined = .out_of_scope };
        const transitive = (try self.wellKnownFact("lessThanTransitive", loc)) orelse
            return .{ .declined = .{ .missing_lemma = "lessThanTransitive" } };

        // 1. peel the forall prefix into fix blocks (eigenvariables), recording
        //    the residual formula at each depth for the forall_intro fold.
        var blocks: std.ArrayList(kernel.BlockId) = .empty;
        var opened: std.ArrayList(TermId) = .empty;
        var parent = block_id;
        var body = goal;
        while (true) {
            const node = self.pool.get(body);
            if (node != .quant or node.quant.q != .forall or node.quant.sort != nat) break;
            const name = try self.freshNamed(self.interner.str(node.quant.hint));
            const fv: term.Node.Fvar = .{ .name = name, .sort = nat };
            const fvt = try self.pool.add(.{ .fvar = fv });
            const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .fix = fv });
            try blocks.append(self.arena, b);
            parent = b;
            body = try self.pool.open(node.quant.body, fvt);
            try opened.append(self.arena, body); // formula proved inside block[k]
        }

        // 2. peel the antecedent chain into assume blocks; restate each as a
        //    hypothesis and collect its strict-order edge.
        var assumes: std.ArrayList(kernel.BlockId) = .empty;
        var residual: std.ArrayList(TermId) = .empty; // formula proved inside assume[k]
        var edges: std.ArrayList(farkas_mod.Edge) = .empty;
        var hyps: std.ArrayList(OrderHyp) = .empty;
        var node_ids: std.ArrayList(TermId) = .empty;
        while (true) {
            const node = self.pool.get(body);
            if (node != .bin or node.bin.op != .implies) break;
            const ante = node.bin.lhs;
            const an = self.pool.get(ante);
            if (an != .pred or !symIs(an.pred.sym, less_than) or an.pred.args_len != 2) return .{ .declined = .out_of_scope };
            const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .assume = ante });
            try assumes.append(self.arena, b);
            parent = b;
            const hyp_ref = try self.emitStep(low, b, loc, ante, .{ .hypothesis = .{ .id = b, .loc = loc } });
            const args = self.pool.args(an.pred);
            try edges.append(self.arena, .{
                .lo = try self.farkasNodeId(&node_ids, args[0]),
                .hi = try self.farkasNodeId(&node_ids, args[1]),
            });
            try hyps.append(self.arena, .{ .lo = args[0], .hi = args[1], .ref = hyp_ref });
            body = node.bin.rhs;
            try residual.append(self.arena, body);
        }
        if (edges.items.len == 0) return .{ .declined = .out_of_scope }; // nothing to combine: not Farkas

        // 2b. COEFFICIENT SCALING (stage 1): if the conclusion mentions a
        //     literal coefficient `mul(k, x)`, derive scaled edges
        //     less_than(mul(k,lo), mul(k,hi)) from each base hypothesis via
        //     multiplicationPreservesOrder, so the fold can line them up.
        const base_count = edges.items.len;
        var literals: std.ArrayList(usize) = .empty;
        try self.collectScaleLiterals(symbols, body, &literals);
        // literals also live in the hypotheses (a hyp `mul(THREE, b) <
        // mul(THREE, a)` while the conclusion is a bare `less_than(a, a)`).
        for (hyps.items) |h| {
            try self.collectScaleLiterals(symbols, h.lo, &literals);
            try self.collectScaleLiterals(symbols, h.hi, &literals);
        }
        if (!try self.emitScaledEdges(low, parent, loc, symbols, literals.items, base_count, &edges, &hyps, &node_ids)) {
            // scaling needed but a lemma/symbol absent: decline (a later stage
            // could report the specific missing_lemma).
            if (literals.items.len != 0) return .{ .declined = .{ .missing_lemma = "multiplicationPreservesOrder" } };
        }

        // 2c. SUM PATH (stage 2): if the conclusion is an add-sum order atom
        //     `less_than(add(_,_), add(_,_))` that no single hypothesis proves,
        //     derive a summed edge from a pair of base hypotheses via
        //     additionPreservesOrder + commutativity + transitivity.
        if (symbols.add) |_| {
            const cn0 = self.pool.get(body);
            const wants_sum = cn0 == .pred and symIs(cn0.pred.sym, less_than) and cn0.pred.args_len == 2 and
                self.isAddSum(symbols, self.pool.args(cn0.pred)[0]);
            if (wants_sum and base_count >= 2) {
                if (try self.trySumEdges(low, parent, loc, symbols, body, base_count, &edges, &hyps, &node_ids)) |missing| {
                    if (missing.len != 0) return .{ .declined = .{ .missing_lemma = missing } };
                }
            }
        }

        // 3+4. prove the conclusion from the order chain, dispatching on its
        //      shape. Three cases:
        //   (a) less_than(s, t), s != t  — ORDER COMPOSITION: fold a path
        //       s < ... < t (no cycle, no irreflexivity).
        //   (b) less_than(x, x)          — the self-loop is the conclusion: a
        //       cycle folds directly to it.
        //   (c) anything else            — INFEASIBILITY CAP: fold a cycle to
        //       less_than(x, x), contradict with lessThanIrreflexive, and
        //       `absurd` proves the (arbitrary) conclusion.
        var carry = (try self.emitFarkasConclusion(low, parent, loc, transitive.formula, transitive.source, less_than, body, edges.items, hyps.items, &node_ids)) orelse
            return .{ .declined = .out_of_scope };

        // 5. export through the assume blocks (implies_intro), then the fix
        //    blocks (forall_intro).
        var ai = assumes.items.len;
        while (ai > 0) {
            ai -= 1;
            _ = try self.emitStep(low, assumes.items[ai], loc, residual.items[ai], carry);
            self.closeBlock(low, assumes.items[ai]);
            carry = .{ .implies_intro = .{ .id = assumes.items[ai], .loc = loc } };
        }
        if (blocks.items.len == 0) return .{ .certified = carry };
        _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, opened.items[opened.items.len - 1], carry);
        var i = blocks.items.len;
        while (i > 1) {
            i -= 1;
            self.closeBlock(low, blocks.items[i]);
            _ = try self.emitStep(low, blocks.items[i - 1], loc, opened.items[i - 1], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
        }
        self.closeBlock(low, blocks.items[0]);
        return .{ .certified = .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } } };
    }

    /// The simplify-rule set `planInner` needs: the well-known recursion
    /// axioms plus the commutativity/left-swap rules (their indices for the
    /// sorted-tower permutation). Shared by the Cooper certifier's arm planner.
    const ArithRules = struct {
        rules: []const simplify_mod.Rule,
        term_rule_count: usize,
        comm_idx: ?usize,
        swap_idx: ?usize,
    };

    fn arithRules(self: *Elaborator, loc: u32) ElabError!?ArithRules {
        var rules: std.ArrayList(simplify_mod.Rule) = .empty;
        for (wk_term_rule_names) |wk| {
            if (try self.wellKnownRule(wk, loc)) |r| try rules.append(self.arena, r);
        }
        if (rules.items.len == 0) return null;
        const term_rule_count = rules.items.len;
        var comm_idx: ?usize = null;
        var swap_idx: ?usize = null;
        if (try self.wellKnownRule("addIsCommutative", loc)) |r| {
            comm_idx = rules.items.len;
            try rules.append(self.arena, r);
        }
        if (try self.wellKnownRule("addLeftSwap", loc)) |r| {
            swap_idx = rules.items.len;
            try rules.append(self.arena, r);
        }
        return .{ .rules = rules.items, .term_rule_count = term_rule_count, .comm_idx = comm_idx, .swap_idx = swap_idx };
    }

    /// A proof of a (possibly disjunctive) body: the inner plan, plus the
    /// or-intro path to lift it into the whole disjunction. `path` is the
    /// sequence of left/right choices from the outside in (empty for a bare
    /// atom), so the emitter wraps the inner proof in that many `or_intro`s.
    const DisjPlan = struct { inner: InnerPlan, path: []const bool, atom: TermId };

    /// Plan a body that may be a right/left nest of `or`: find the first arm an
    /// InnerPlan certifies, recording the or-intro path to it. Returns null when
    /// no arm is provable.
    fn planDisjunction(self: *Elaborator, symbols: presburger_mod.Symbols, ar: ArithRules, body: TermId, loc: u32) ElabError!?DisjPlan {
        var path: std.ArrayList(bool) = .empty;
        var cur = body;
        while (true) {
            const node = self.pool.get(cur);
            if (node == .bin and node.bin.op == .or_op) {
                // try the left arm (path so far + left), else descend right.
                try path.append(self.arena, false);
                if (try self.planInner(symbols, ar.rules, ar.term_rule_count, ar.comm_idx, ar.swap_idx, node.bin.lhs, loc)) |inner| {
                    return .{ .inner = inner, .path = try self.arena.dupe(bool, path.items), .atom = node.bin.lhs };
                }
                _ = path.pop();
                try path.append(self.arena, true);
                cur = node.bin.rhs;
                continue;
            }
            if (try self.planInner(symbols, ar.rules, ar.term_rule_count, ar.comm_idx, ar.swap_idx, cur, loc)) |inner| {
                return .{ .inner = inner, .path = try self.arena.dupe(bool, path.items), .atom = cur };
            }
            return null;
        }
    }

    /// Reconstruct a boundary witness `boundaries[i] + j` (a linear form over
    /// the fixed variables) as a Nat term. Layer 2 handles the single-free-
    /// variable case: coeff 0 (a constant `succ^(konst+j)(ZERO)`) or coeff 1 on
    /// the one eigenvariable (`succ^(konst+j)(x)`). A negative total offset or a
    /// higher coefficient is not a buildable Nat term — return null (that
    /// candidate is skipped).
    fn buildWitness(self: *Elaborator, symbols: presburger_mod.Symbols, replay: presburger_mod.Replay, dump: presburger_mod.LinearDump, j: i128, fix_vars: []const term.Node.Fvar) ElabError!?TermId {
        // find the (at most one) free var with a nonzero coefficient. A boundary
        // coeff is indexed by presburger variable id; `free_ids[p]` is the id of
        // the p-th free var, which corresponds to fix_vars[p] (both in first-
        // appearance / forall-binder order).
        var fix_index: ?usize = null;
        for (dump.coeffs, 0..) |co, id| {
            if (co == 0) continue;
            if (co != 1) return null; // coeff>1: out of layer-2 scope
            // locate this id among the free vars
            const p = std.mem.indexOfScalar(u32, replay.free_ids, @intCast(id)) orelse return null;
            if (fix_index != null) return null; // 2+ free vars in the witness
            fix_index = p;
        }
        const offset = dump.konst + j;
        if (offset < 0) return null;
        const succs: usize = @intCast(offset);
        const zero_sym = symbols.zero orelse return null;
        const base = if (fix_index) |p| blk: {
            if (p >= fix_vars.len) return null;
            break :blk try self.pool.add(.{ .fvar = fix_vars[p] });
        } else try self.pool.addApp(.app, zero_sym, &.{});
        return try self.buildTower(symbols, succs, base);
    }

    /// Prove `exists_body` (an `exists y; disjunction`) in `block` by finding a
    /// witness (from `candidates`) whose opened body — a right/left nest of
    /// `or` — has a provable arm (equation/order, under `premises`). Emits the
    /// arm proof, lifts it through the or-intro path, and returns the
    /// `exists_intro` justification (NOT yet emitted as a step). Returns null
    /// when no candidate witness proves the body. Shared by the period-1 layer,
    /// the induction base case, and each induction step arm.
    fn emitExistsWitness(
        self: *Elaborator,
        low: *Lowering,
        block: kernel.BlockId,
        exists_body: TermId, // exists y; disj
        candidates: []const TermId,
        ar: ArithRules,
        symbols: presburger_mod.Symbols,
        premises: []CertPremise,
        loc: u32,
    ) ElabError!?kernel.Justification {
        _ = ar;
        const en = self.pool.get(exists_body);
        if (en != .quant or en.quant.q != .exists) return null;
        for (candidates) |witness| {
            const instance = try self.pool.open(en.quant.body, witness);
            // find a provable arm of the (possibly disjunctive) instance; prove
            // it via arithCertCore (which handles the cited premises), then lift
            // through the or-intro path.
            const found = (try self.proveDisjArm(low, block, instance, symbols, premises, loc)) orelse continue;
            var arm_ref = found.ref;
            var pi = found.path.len;
            while (pi > 0) {
                pi -= 1;
                const disj = try self.disjunctionAt(instance, found.path[0..pi]);
                const just: kernel.Justification = if (found.path[pi])
                    .{ .or_intro_right = arm_ref }
                else
                    .{ .or_intro_left = arm_ref };
                arm_ref = try self.emitStep(low, block, loc, disj, just);
            }
            return .{ .exists_intro = .{ .step = arm_ref, .witness = witness, .witness_loc = loc } };
        }
        return null;
    }

    /// Prove one arm of a right/left `or`-nest `instance` via arithCertCore
    /// (using `premises`), emitting the arm's proof step. Returns the arm's
    /// step ref and the or-intro path to it, or null if no arm is provable.
    fn proveDisjArm(
        self: *Elaborator,
        low: *Lowering,
        block: kernel.BlockId,
        instance: TermId,
        symbols: presburger_mod.Symbols,
        premises: []CertPremise,
        loc: u32,
    ) ElabError!?struct { ref: kernel.SRef, path: []const bool } {
        var path: std.ArrayList(bool) = .empty;
        var cur = instance;
        while (true) {
            const node = self.pool.get(cur);
            if (node == .bin and node.bin.op == .or_op) {
                if (try self.arithCertCore(low, block, node.bin.lhs, premises, symbols, loc)) |just| {
                    const ref = try self.emitStep(low, block, loc, node.bin.lhs, just);
                    try path.append(self.arena, false);
                    return .{ .ref = ref, .path = try self.arena.dupe(bool, path.items) };
                }
                try path.append(self.arena, true);
                cur = node.bin.rhs;
                continue;
            }
            if (try self.arithCertCore(low, block, cur, premises, symbols, loc)) |just| {
                const ref = try self.emitStep(low, block, loc, cur, just);
                return .{ .ref = ref, .path = try self.arena.dupe(bool, path.items) };
            }
            return null;
        }
    }

    /// The Cooper certifier link (layers 2-3). Layer 2 (period 1): pick a
    /// boundary witness and prove the body directly. Layer 3 (period > 1):
    /// synthesize an induction on the fixed variable (the periodicity/−∞
    /// residue is provable over Nat only inductively). Nested/multi-var
    /// alternation declines (out of scope).
    fn cooperCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
        _ = c;
        if (symbols.nat == null) return .{ .declined = .out_of_scope };

        // peel the forall prefix; the body must be `exists y; …`
        const u = try self.peelUniversal(goal, "cooper");
        const body_node = self.pool.get(u.body);
        if (body_node != .quant or body_node.quant.q != .exists) return .{ .declined = .out_of_scope };

        // record the Cooper elimination of the single existential
        const traced = try presburger_mod.trace(self.arena, self.pool, symbols, &.{}, u.body);
        if (traced != .replay) return .{ .declined = .out_of_scope };
        const replay = traced.replay;

        const ar = (try self.arithRules(loc)) orelse return .{ .declined = .{ .missing_lemma = "addZeroLeft" } };

        if (replay.period != 1) return self.cooperInduction(low, block_id, u, symbols, ar, loc);

        // period 1: the boundary witnesses (reconstructed as Nat terms) are the
        // candidate witnesses; prove the body at the first that works.
        var candidates: std.ArrayList(TermId) = .empty;
        for (replay.disjuncts) |d| {
            const bw = switch (d) {
                .minus_inf => continue,
                .boundary => |b| b,
            };
            if (try self.buildWitness(symbols, replay, replay.boundaries[bw.b_index], bw.j, u.fix_vars)) |w| {
                try candidates.append(self.arena, w);
            }
        }
        const carry = (try self.emitExistsWitnessInFix(low, block_id, u, u.body, candidates.items, ar, symbols, loc)) orelse
            return .{ .declined = .out_of_scope };
        return .{ .certified = carry };
    }

    /// Emit `u.body` (an existential) inside the peeled forall's fix blocks and
    /// fold back out with forall_intro. `exists_body` is proved by
    /// `emitExistsWitness` at one of `candidates`.
    fn emitExistsWitnessInFix(
        self: *Elaborator,
        low: *Lowering,
        block_id: kernel.BlockId,
        u: Universal,
        exists_body: TermId,
        candidates: []const TermId,
        ar: ArithRules,
        symbols: presburger_mod.Symbols,
        loc: u32,
    ) ElabError!?kernel.Justification {
        var blocks: std.ArrayList(kernel.BlockId) = .empty;
        var parent = block_id;
        for (u.fix_vars) |fv| {
            const b = try self.newBlock(low, try self.freshNamed("cooper"), parent, .{ .fix = fv });
            try blocks.append(self.arena, b);
            parent = b;
        }
        const carry = (try self.emitExistsWitness(low, parent, exists_body, candidates, ar, symbols, &.{}, loc)) orelse return null;
        if (blocks.items.len == 0) return carry;
        _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, exists_body, carry);
        var i = blocks.items.len;
        while (i > 1) {
            i -= 1;
            self.closeBlock(low, blocks.items[i]);
            _ = try self.emitStep(low, blocks.items[i - 1], loc, u.opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
        }
        self.closeBlock(low, blocks.items[0]);
        return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
    }

    /// Candidate existential witnesses for the induction base/step, built from
    /// the fixed vars (`ZERO`, small towers) and, in the step, the unpacked IH
    /// witness `y0` (`y0`, `succ(y0)`, `succ(succ(y0))`). The shift table for
    /// arbitrary period is realized by this bounded search: one of these proves
    /// the residue-class arm at succ(k).
    fn witnessCandidates(self: *Elaborator, symbols: presburger_mod.Symbols, ih_witness: ?TermId) ElabError![]const TermId {
        var out: std.ArrayList(TermId) = .empty;
        const zero_sym = symbols.zero orelse return out.items;
        const zero = try self.pool.addApp(.app, zero_sym, &.{});
        // constant towers ZERO..3 (base case classes)
        for (0..4) |k| {
            if (try self.buildTower(symbols, k, zero)) |w| try out.append(self.arena, w);
        }
        // shifted IH witness (step case classes)
        if (ih_witness) |y0| {
            for (0..3) |k| {
                if (try self.buildTower(symbols, k, y0)) |w| try out.append(self.arena, w);
            }
        }
        return out.items;
    }

    /// Layer 3: synthesize an induction on the single fixed variable to certify
    /// a period-D `forall x; exists y; body`. Predicate P(k) = body[x:=k];
    /// base P(ZERO) and step `forall k; P(k) -> P(succ(k))` are proved by the
    /// witness search (the step unpacks the IH witness and case-splits its
    /// disjunction, shifting the witness per arm), then `induction` is
    /// instantiated at P. Declines (out_of_scope) on multi-variable goals.
    fn cooperInduction(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, u: Universal, symbols: presburger_mod.Symbols, ar: ArithRules, loc: u32) ElabError!Outcome {
        // layer 3 handles a single fixed variable (the induction variable).
        if (u.fix_vars.len != 1) return .{ .declined = .out_of_scope };
        const nat = symbols.nat.?;

        // the induction schema must be in scope (a parameterized axiom = a
        // proofless schema); resolve it for the instance construction.
        const induction_id = self.env.findStatementId(self.theoryScope(), self.interner.intern("induction") catch return error.OutOfMemory) orelse
            return .{ .declined = .{ .missing_lemma = "induction" } };
        const induction_stmt = &self.env.statements.items[@intFromEnum(induction_id)];
        if (induction_stmt.* != .schema or induction_stmt.schema.proof != null) return .{ .declined = .{ .missing_lemma = "induction" } };

        // P as a closed body over the induction variable: P[t] = open(P_closed, t)
        const x = u.fix_vars[0];
        const x_id = try self.pool.add(.{ .fvar = x });
        const p_closed = try self.pool.close(u.body, x.name);

        const zero_sym = symbols.zero orelse return .{ .declined = .{ .missing_symbol = "ZERO" } };
        const succ_sym = symbols.succ orelse return .{ .declined = .{ .missing_symbol = "succ" } };

        // --- base case: P(ZERO) ------------------------------------------
        const zero = try self.pool.addApp(.app, zero_sym, &.{});
        const p_zero = try self.pool.open(p_closed, zero);
        const base_candidates = try self.witnessCandidates(symbols, null);
        const base_just = (try self.emitExistsWitness(low, block_id, p_zero, base_candidates, ar, symbols, &.{}, loc)) orelse
            return .{ .declined = .out_of_scope };
        const base_ref = try self.emitStep(low, block_id, loc, p_zero, base_just);

        // --- step: forall k; P(k) -> P(succ(k)) --------------------------
        const k: term.Node.Fvar = .{ .name = try self.freshNamed("k"), .sort = nat };
        const k_id = try self.pool.add(.{ .fvar = k });
        const p_k = try self.pool.open(p_closed, k_id);
        const succ_k = try self.pool.addApp(.app, succ_sym, &.{k_id});
        const p_succ_k = try self.pool.open(p_closed, succ_k);
        const step_impl_open = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = p_k, .rhs = p_succ_k } });
        const step_forall = try self.closeForall(step_impl_open, k, nat);

        const fix_k = try self.newBlock(low, try self.freshNamed("induction-step"), block_id, .{ .fix = k });
        const assume_pk = try self.newBlock(low, try self.freshNamed("given-inductive-hypothesis"), fix_k, .{ .assume = p_k });
        const ih_ref = try self.emitStep(low, assume_pk, loc, p_k, .{ .hypothesis = .{ .id = assume_pk, .loc = loc } });

        // unpack the IH existential witness y0
        const ih_ex = self.pool.get(p_k);
        if (ih_ex != .quant or ih_ex.quant.q != .exists) return .{ .declined = .out_of_scope };
        const y0: term.Node.Fvar = .{ .name = try self.freshNamed("y"), .sort = ih_ex.quant.sort };
        const y0_id = try self.pool.add(.{ .fvar = y0 });
        const ih_body = try self.pool.open(ih_ex.quant.body, y0_id); // the disjunction at y0
        const unpack_block = try self.newBlock(low, try self.freshNamed("with-witness-y"), assume_pk, .{ .unpack = .{ .v = y0, .source = ih_ref } });
        const ih_body_ref = try self.emitStep(low, unpack_block, loc, ih_body, .{ .hypothesis = .{ .id = unpack_block, .loc = loc } });

        // prove P(succ(k)) by case-splitting ih_body; each arm gives a case
        // hypothesis (an equation over k, y0) used as a premise for the witness
        // search on P(succ(k)).
        const step_candidates = try self.witnessCandidates(symbols, y0_id);
        const case_just = (try self.emitInductionCases(low, unpack_block, ih_body, ih_body_ref, p_succ_k, step_candidates, ar, symbols, loc)) orelse
            return .{ .declined = .out_of_scope };
        _ = try self.emitStep(low, unpack_block, loc, p_succ_k, case_just);
        self.closeBlock(low, unpack_block);

        // export P(succ(k)) out of the unpack (exists_elim), the assume
        // (implies_intro), and the fix (forall_intro).
        _ = try self.emitStep(low, assume_pk, loc, p_succ_k, .{ .exists_elim = .{ .id = unpack_block, .loc = loc } });
        self.closeBlock(low, assume_pk);
        _ = try self.emitStep(low, fix_k, loc, step_impl_open, .{ .implies_intro = .{ .id = assume_pk, .loc = loc } });
        self.closeBlock(low, fix_k);
        const step_ref = try self.emitStep(low, block_id, loc, step_forall, .{ .forall_intro = .{ .id = fix_k, .loc = loc } });

        // --- instantiate induction at P ----------------------------------
        const instance = (try self.instantiateInduction(induction_id, &induction_stmt.schema, p_closed, nat, loc)) orelse
            return .{ .declined = .out_of_scope };
        // the instance concludes `forall n; P(n)`, which is exactly the goal
        // (alpha-equal). Cite base and step as the two premises.
        const premises = try self.arena.dupe(kernel.SRef, &.{ base_ref, step_ref });
        _ = x_id;
        return .{ .certified = .{ .schema_instance = .{ .instance = instance, .premises = premises } } };
    }

    /// Wrap `body` (mentioning fvar `v`) in `forall v.name; …`.
    fn closeForall(self: *Elaborator, body: TermId, v: term.Node.Fvar, sort: term.SortId) ElabError!TermId {
        const closed = try self.pool.close(body, v.name);
        return self.pool.add(.{ .quant = .{ .q = .forall, .sort = sort, .hint = v.name, .body = closed } });
    }

    /// Prove `goal` (= P(succ(k))) by an or_elim over `disj` (the IH witness
    /// disjunction at y0). Each arm assumes one disjunct — an equation over
    /// k, y0 — and proves `goal` by the witness search using that equation as a
    /// rewrite premise. Returns the or_elim justification, or null if any arm
    /// fails. Handles a right-nested chain of `or` recursively.
    fn emitInductionCases(
        self: *Elaborator,
        low: *Lowering,
        parent: kernel.BlockId,
        disj: TermId,
        disj_ref: kernel.SRef,
        goal: TermId,
        candidates: []const TermId,
        ar: ArithRules,
        symbols: presburger_mod.Symbols,
        loc: u32,
    ) ElabError!?kernel.Justification {
        const node = self.pool.get(disj);
        if (node != .bin or node.bin.op != .or_op) return null;

        // left arm: assume the lhs disjunct, prove goal at some witness.
        const left = try self.newBlock(low, try self.freshNamed("when-even"), parent, .{ .assume = node.bin.lhs });
        const lhyp = try self.emitStep(low, left, loc, node.bin.lhs, .{ .hypothesis = .{ .id = left, .loc = loc } });
        const lprem = try self.arena.dupe(CertPremise, &.{.{ .formula = node.bin.lhs, .step = lhyp, .statement = null, .rule_idx = undefined, .elim = null }});
        const ljust = (try self.emitExistsWitness(low, left, goal, candidates, ar, symbols, lprem, loc)) orelse return null;
        _ = try self.emitStep(low, left, loc, goal, ljust);
        self.closeBlock(low, left);

        // right arm: the rhs disjunct (possibly itself an or, recursed).
        const right = try self.newBlock(low, try self.freshNamed("when-odd"), parent, .{ .assume = node.bin.rhs });
        const rhyp = try self.emitStep(low, right, loc, node.bin.rhs, .{ .hypothesis = .{ .id = right, .loc = loc } });
        const rn = self.pool.get(node.bin.rhs);
        if (rn == .bin and rn.bin.op == .or_op) {
            const inner = (try self.emitInductionCases(low, right, node.bin.rhs, rhyp, goal, candidates, ar, symbols, loc)) orelse return null;
            _ = try self.emitStep(low, right, loc, goal, inner);
        } else {
            const rprem = try self.arena.dupe(CertPremise, &.{.{ .formula = node.bin.rhs, .step = rhyp, .statement = null, .rule_idx = undefined, .elim = null }});
            const rjust = (try self.emitExistsWitness(low, right, goal, candidates, ar, symbols, rprem, loc)) orelse return null;
            _ = try self.emitStep(low, right, loc, goal, rjust);
        }
        self.closeBlock(low, right);

        return .{ .or_elim = .{ .disj = disj_ref, .left = .{ .id = left, .loc = loc }, .right = .{ .id = right, .loc = loc } } };
    }

    /// Instantiate the `induction` schema at predicate `p_closed` (a body closed
    /// over the induction variable), producing the instance formula
    /// `P(ZERO) -> (forall k; P(k) -> P(succ(k))) -> forall n; P(n)`.
    fn instantiateInduction(self: *Elaborator, induction_id: StatementId, schema: *const Statement.Schema, p_closed: TermId, nat: term.SortId, loc: u32) ElabError!?TermId {
        _ = loc;
        if (schema.params.len != 1) return null;
        const pname = try self.internTok(schema.params[0].name);
        var args_map: SchemaArgs = .empty;
        args_map.put(self.arena, pname, .{ .lambda = .{ .body = p_closed, .arg_sort = nat, .result_sort = .prop } }) catch return error.OutOfMemory;
        const schema_ctx: Ctx = .{ .source = schema.source, .file = schema.file, .diag = @intFromEnum(schema.file) };
        return self.instantiateSchemaCore(induction_id, schema, schema_ctx, &args_map);
    }

    /// Descend `instance` (a right/left nest of `or`) along `path` to the
    /// sub-disjunction at that prefix. `path` is left(false)/right(true) steps.
    fn disjunctionAt(self: *Elaborator, instance: TermId, path: []const bool) ElabError!TermId {
        var cur = instance;
        for (path) |go_right| {
            const node = self.pool.get(cur);
            cur = if (go_right) node.bin.rhs else node.bin.lhs;
        }
        return cur;
    }

    /// If `t` is a ground successor tower over ZERO (`succ^k(ZERO)`), return k.
    /// Used to recognize literal coefficients `mul(k, x)` for Farkas scaling.
    fn farkasLiteral(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) usize {
        var k: usize = 0;
        var cur = t;
        while (true) {
            const node = self.pool.get(cur);
            if (node == .app and symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
                k += 1;
                cur = self.pool.args(node.app)[0];
                continue;
            }
            if (node == .app and symIs(node.app.sym, symbols.zero) and node.app.args_len == 0) return k;
            return 0; // not a ground ZERO-tower
        }
    }

    /// Scan `t` for `mul(<literal>, x)` subterms, collecting the distinct
    /// literal coefficients k >= 2 (k = 1 is a no-op scale; k = 0 degenerate).
    fn collectScaleLiterals(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId, out: *std.ArrayList(usize)) ElabError!void {
        const node = self.pool.get(t);
        switch (node) {
            .app, .pred => |a| {
                if (symIs(a.sym, symbols.mul) and a.args_len == 2) {
                    const args = self.pool.args(a);
                    const k = self.farkasLiteral(symbols, args[0]);
                    if (k >= 2) {
                        for (out.items) |x| {
                            if (x == k) break;
                        } else try out.append(self.arena, k);
                    }
                }
                for (self.pool.args(a)) |arg| try self.collectScaleLiterals(symbols, arg, out);
            },
            .eq => |p| {
                try self.collectScaleLiterals(symbols, p.lhs, out);
                try self.collectScaleLiterals(symbols, p.rhs, out);
            },
            .not => |inner| try self.collectScaleLiterals(symbols, inner, out),
            .bin => |b| {
                try self.collectScaleLiterals(symbols, b.lhs, out);
                try self.collectScaleLiterals(symbols, b.rhs, out);
            },
            .quant => |q| try self.collectScaleLiterals(symbols, q.body, out),
            else => {},
        }
    }

    /// Is `t` an `add(_, _)` application?
    fn isAddSum(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) bool {
        const node = self.pool.get(t);
        return node == .app and symIs(node.app.sym, symbols.add) and node.app.args_len == 2;
    }

    /// The conclusion is `less_than(add(A,B), add(C,D))`. Find base hypotheses
    /// proving A<C and B<D, emit their summed edge (A+B < C+D), and append it.
    /// Returns null on success, or a non-empty missing-lemma name if a needed
    /// lemma is absent (so the caller declines with that reason). Returns an
    /// empty slice when the shape simply doesn't match (fall through quietly).
    fn trySumEdges(
        self: *Elaborator,
        low: *Lowering,
        block: kernel.BlockId,
        loc: u32,
        symbols: presburger_mod.Symbols,
        body: TermId,
        base_count: usize,
        edges: *std.ArrayList(farkas_mod.Edge),
        hyps: *std.ArrayList(OrderHyp),
        node_ids: *std.ArrayList(TermId),
    ) ElabError!?[]const u8 {
        const cargs = self.pool.args(self.pool.get(body).pred);
        const lhs = self.pool.args(self.pool.get(cargs[0]).app); // [A, B]
        const rhs = self.pool.args(self.pool.get(cargs[1]).app); // [C, D]
        const a = lhs[0];
        const bb = lhs[1];
        const cc = rhs[0];
        const dd = rhs[1];
        // find base hyps A<C and B<D
        var ha: ?OrderHyp = null;
        var hb: ?OrderHyp = null;
        for (hyps.items[0..base_count]) |h| {
            if (self.pool.termOrder(h.lo, a) == .eq and self.pool.termOrder(h.hi, cc) == .eq) ha = h;
            if (self.pool.termOrder(h.lo, bb) == .eq and self.pool.termOrder(h.hi, dd) == .eq) hb = h;
        }
        const first = ha orelse return &.{};
        const second = hb orelse return &.{};

        const apo = (try self.wellKnownFact("additionPreservesOrder", loc)) orelse return "additionPreservesOrder";
        const comm = (try self.wellKnownRule("addIsCommutative", loc)) orelse return "addIsCommutative";
        const transitive = (try self.wellKnownFact("lessThanTransitive", loc)) orelse return "lessThanTransitive";

        const summed = try self.emitSumEdge(low, block, loc, symbols, apo.formula, apo.source, comm, transitive.formula, transitive.source, first, second);
        try edges.append(self.arena, .{
            .lo = try self.farkasNodeId(node_ids, summed.lo),
            .hi = try self.farkasNodeId(node_ids, summed.hi),
        });
        try hyps.append(self.arena, summed);
        return null;
    }

    /// Emit a SUMMED edge from two order hypotheses ha (p<q) and hb (r<s):
    /// prove `less_than(add(p,r), add(q,s))` and return it as an OrderHyp.
    /// Follows the verified chain (see tests): lift p<q by +r via
    /// additionPreservesOrder and commute to `add(p,r)<add(q,r)`; lift r<s by
    /// +q to `add(q,r)<add(q,s)`; chain with lessThanTransitive.
    fn emitSumEdge(
        self: *Elaborator,
        low: *Lowering,
        block: kernel.BlockId,
        loc: u32,
        symbols: presburger_mod.Symbols,
        apo_formula: TermId, // additionPreservesOrder
        apo_source: simplify_mod.Source,
        comm: simplify_mod.Rule, // addIsCommutative as a rewrite rule
        transitive_formula: TermId,
        transitive_source: simplify_mod.Source,
        ha: OrderHyp,
        hb: OrderHyp,
    ) ElabError!OrderHyp {
        const add = symbols.add.?;
        const p = ha.lo;
        const q = ha.hi;
        const r = hb.lo;
        const s = hb.hi;

        // additionPreservesOrder binders (c, b, a); body
        //   less_than(a,b) -> less_than(add(c,a), add(c,b)).
        // lift p<q by c:=r -> forall_elim(r, q, p): add(r,p)<add(r,q)
        const apo_rule1 = try self.strippedRule(apo_formula, apo_source);
        const imp1 = try self.emitInstance(low, block, loc, apo_rule1, &.{ r, q, p });
        const lifted1 = self.pool.get(low.steps.items[@intFromEnum(imp1.id)].formula).bin.rhs;
        const rp_lt_rq = try self.emitStep(low, block, loc, lifted1, .{ .modus_ponens = .{ .implication = imp1, .antecedent = ha.ref } });

        // commute add(r,p)=add(p,r) and add(r,q)=add(q,r), rewrite both.
        const rp = try self.pool.addApp(.app, add, &.{ r, p });
        const pr = try self.pool.addApp(.app, add, &.{ p, r });
        const rq = try self.pool.addApp(.app, add, &.{ r, q });
        const qr = try self.pool.addApp(.app, add, &.{ q, r });
        const eq_rp = try self.emitCommEq(low, block, loc, comm, rp, pr); // add(r,p)=add(p,r)
        const eq_rq = try self.emitCommEq(low, block, loc, comm, rq, qr); // add(r,q)=add(q,r)
        // rewrite rp_lt_rq: add(r,p)<add(r,q)  ->  add(p,r)<add(q,r)
        const pr_lt_rq_f = try self.pool.addApp(.pred, symbols.less_than.?, &.{ pr, rq });
        const pr_lt_rq = try self.emitStep(low, block, loc, pr_lt_rq_f, .{ .rewrite = .{ .equation = eq_rp, .target = rp_lt_rq } });
        const pr_lt_qr_f = try self.pool.addApp(.pred, symbols.less_than.?, &.{ pr, qr });
        const pr_lt_qr = try self.emitStep(low, block, loc, pr_lt_qr_f, .{ .rewrite = .{ .equation = eq_rq, .target = pr_lt_rq } });

        // lift r<s by c:=q -> forall_elim(q, s, r): add(q,r)<add(q,s)
        const apo_rule2 = try self.strippedRule(apo_formula, apo_source);
        const imp2 = try self.emitInstance(low, block, loc, apo_rule2, &.{ q, s, r });
        const lifted2 = self.pool.get(low.steps.items[@intFromEnum(imp2.id)].formula).bin.rhs;
        const qr_lt_qs = try self.emitStep(low, block, loc, lifted2, .{ .modus_ponens = .{ .implication = imp2, .antecedent = hb.ref } });

        // chain add(p,r) < add(q,r) < add(q,s) via lessThanTransitive
        const qs = try self.pool.addApp(.app, add, &.{ q, s });
        const tr_rule = try self.strippedRule(transitive_formula, transitive_source);
        const chain = try self.emitInstance(low, block, loc, tr_rule, &.{ qs, qr, pr });
        const chain_inner = self.pool.get(low.steps.items[@intFromEnum(chain.id)].formula).bin.rhs;
        const chain2 = try self.emitStep(low, block, loc, chain_inner, .{ .modus_ponens = .{ .implication = chain, .antecedent = pr_lt_qr } });
        const summed_f = self.pool.get(chain_inner).bin.rhs;
        const summed = try self.emitStep(low, block, loc, summed_f, .{ .modus_ponens = .{ .implication = chain2, .antecedent = qr_lt_qs } });
        return .{ .lo = pr, .hi = qs, .ref = summed };
    }

    /// Emit `lhs = rhs` where they differ by one addIsCommutative rewrite,
    /// using the comm rule instantiated to the right pair.
    fn emitCommEq(self: *Elaborator, low: *Lowering, block: kernel.BlockId, loc: u32, comm: simplify_mod.Rule, lhs: TermId, rhs: TermId) ElabError!kernel.SRef {
        // comm: forall b, a; add(a, b) = add(b, a). lhs = add(x, y), want
        // add(x,y) = add(y,x): match a:=x, b:=y -> forall_elim(b:=y, a:=x).
        _ = rhs; // determined by the instance; named for the caller's clarity
        const la = self.pool.args(self.pool.get(lhs).app);
        return self.emitInstance(low, block, loc, comm, &.{ la[1], la[0] });
    }

    /// For each base order hypothesis and each literal k in `literals`, emit a
    /// SCALED edge `less_than(mul(k,lo), mul(k,hi))` via
    /// multiplicationPreservesOrder (k = succ(c), so forall_elim at c =
    /// succ^{k-1}(ZERO)), appending it to `edges`/`hyps`/`node_ids`. Returns
    /// false (declines) if `multiplicationPreservesOrder` or `mul`/`succ`/`zero`
    /// are absent. The scaled edges then feed the same fold as base edges.
    fn emitScaledEdges(
        self: *Elaborator,
        low: *Lowering,
        block: kernel.BlockId,
        loc: u32,
        symbols: presburger_mod.Symbols,
        literals: []const usize,
        base_count: usize,
        edges: *std.ArrayList(farkas_mod.Edge),
        hyps: *std.ArrayList(OrderHyp),
        node_ids: *std.ArrayList(TermId),
    ) ElabError!bool {
        if (literals.len == 0) return true;
        const succ = symbols.succ orelse return false;
        const zero_sym = symbols.zero orelse return false;
        const mpo = (try self.wellKnownFact("multiplicationPreservesOrder", loc)) orelse return false;
        const zero = try self.pool.addApp(.app, zero_sym, &.{});

        for (literals) |k| {
            // c = succ^{k-1}(ZERO), so succ(c) = k
            var c = zero;
            for (0..k - 1) |_| c = try self.pool.addApp(.app, succ, &.{c});
            for (0..base_count) |bi| {
                const h = hyps.items[bi];
                // multiplicationPreservesOrder binders (c, b, a); body
                //   less_than(a,b) -> less_than(mul(succ(c),a), mul(succ(c),b)).
                // want a:=h.lo, b:=h.hi, c:=c -> forall_elim(c, h.hi, h.lo).
                const rule = try self.strippedRule(mpo.formula, mpo.source);
                const imp = try self.emitInstance(low, block, loc, rule, &.{ c, h.hi, h.lo });
                const concl = self.pool.get(low.steps.items[@intFromEnum(imp.id)].formula).bin.rhs;
                const scaled_ref = try self.emitStep(low, block, loc, concl, .{ .modus_ponens = .{ .implication = imp, .antecedent = h.ref } });
                const scaled = self.pool.get(concl).pred;
                const sargs = self.pool.args(scaled);
                try edges.append(self.arena, .{
                    .lo = try self.farkasNodeId(node_ids, sargs[0]),
                    .hi = try self.farkasNodeId(node_ids, sargs[1]),
                });
                try hyps.append(self.arena, .{ .lo = sargs[0], .hi = sargs[1], .ref = scaled_ref });
            }
        }
        return true;
    }

    /// Prove the Farkas conclusion `body` from the order hypotheses, returning
    /// the justification of a step proving `body` in `block` (or null to
    /// decline). Dispatches on the conclusion shape (see the call site).
    fn emitFarkasConclusion(
        self: *Elaborator,
        low: *Lowering,
        block: kernel.BlockId,
        loc: u32,
        transitive_formula: TermId,
        transitive_source: simplify_mod.Source,
        less_than: term.SymId,
        body: TermId,
        edges: []const farkas_mod.Edge,
        hyps: []const OrderHyp,
        node_ids: *std.ArrayList(TermId),
    ) ElabError!?kernel.Justification {
        const cn = self.pool.get(body);
        const is_order = cn == .pred and symIs(cn.pred.sym, less_than) and cn.pred.args_len == 2;

        // (a)/(b) ORDER COMPOSITION: if the conclusion is an order atom
        // less_than(s, t), try to compose a chain s < ... < t directly (a cycle
        // when s == t). This is preferred — no irreflexivity needed.
        if (is_order) {
            const cargs = self.pool.args(cn.pred);
            const from = try self.farkasNodeId(node_ids, cargs[0]);
            const to = try self.farkasNodeId(node_ids, cargs[1]);
            if (try farkas_mod.compose(self.arena, edges, from, to)) |path| {
                const proof = try self.emitFarkasFold(low, block, loc, transitive_formula, transitive_source, path.chain, hyps);
                return low.steps.items[@intFromEnum(proof.id)].just;
            }
            // no direct chain: fall through to the infeasibility cap (the
            // hypotheses may be contradictory, proving any conclusion).
        }

        // (c) INFEASIBILITY CAP: fold ANY cycle to less_than(x, x), contradict
        // with lessThanIrreflexive, and `absurd` proves the (arbitrary) `body`
        // — including an order atom that has no direct chain (e.g. a scaled
        // cycle proving less_than(a, a) for a bare a not on the cycle).
        const irreflexive = (try self.wellKnownFact("lessThanIrreflexive", loc)) orelse return null;
        const refutation = (try farkas_mod.refute(self.arena, edges, null)) orelse return null;
        const proof = try self.emitFarkasFold(low, block, loc, transitive_formula, transitive_source, refutation.chain, hyps);
        const cnode = node_ids.items[refutation.node];
        // emitInstance specializes lessThanIrreflexive at cnode to
        // `not less_than(cnode, cnode)`; absurd against the folded
        // `less_than(cnode, cnode)` then proves the (arbitrary) conclusion.
        const irr_rule = try self.strippedRule(irreflexive.formula, irreflexive.source);
        const not_ref = try self.emitInstance(low, block, loc, irr_rule, &.{cnode});
        return .{ .absurd = .{ .s1 = proof, .s2 = not_ref } };
    }

    /// Intern a term as an abstract Farkas node identity (by structural order).
    fn farkasNodeId(self: *Elaborator, list: *std.ArrayList(TermId), t: TermId) ElabError!usize {
        for (list.items, 0..) |x, i| {
            if (self.pool.termOrder(x, t) == .eq) return i;
        }
        try list.append(self.arena, t);
        return list.items.len - 1;
    }

    /// Fold an order chain (edge indices, each hi linking to the next lo) into
    /// a single proof `less_than(chain-first-lo, chain-last-hi)` by composing
    /// consecutive hypotheses with lessThanTransitive. Returns the step ref of
    /// that proof (the sole hypothesis when the chain has one edge).
    fn emitFarkasFold(
        self: *Elaborator,
        low: *Lowering,
        block: kernel.BlockId,
        loc: u32,
        transitive_formula: TermId,
        transitive_source: simplify_mod.Source,
        chain: []const usize,
        hyps: []const OrderHyp,
    ) ElabError!kernel.SRef {
        // running proof `acc_ref`: less_than(acc_lo, acc_hi)
        var acc_ref = hyps[chain[0]].ref;
        const acc_lo = hyps[chain[0]].lo;
        var acc_hi = hyps[chain[0]].hi;

        for (chain[1..]) |idx| {
            const next = hyps[idx];
            // lessThanTransitive has binders `forall c, b, a` over body
            //   less_than(a, b) -> less_than(b, c) -> less_than(a, c).
            // We want a:=acc_lo, b:=acc_hi, c:=next.hi, so specialize in
            // binder order (c, b, a) = (next.hi, acc_hi, acc_lo).
            const rule = try self.strippedRule(transitive_formula, transitive_source);
            const imp3 = try self.emitInstance(low, block, loc, rule, &.{ next.hi, acc_hi, acc_lo });
            // apply to the two order proofs: modus_ponens twice
            const inner = self.pool.get(low.steps.items[@intFromEnum(imp3.id)].formula).bin.rhs;
            const imp2 = try self.emitStep(low, block, loc, inner, .{ .modus_ponens = .{ .implication = imp3, .antecedent = acc_ref } });
            const concl = self.pool.get(inner).bin.rhs;
            acc_ref = try self.emitStep(low, block, loc, concl, .{ .modus_ponens = .{ .implication = imp2, .antecedent = next.ref } });
            acc_hi = next.hi;
        }
        return acc_ref;
    }

    /// For a NAMED theory: does the goal/premises use an arithmetic symbol the
    /// theory failed to provide? Returns its (well-known) name if so. A symbol
    /// USED in the goal but whose theory-resolved counterpart is null would be
    /// treated as an opaque foreign atom — a silent failure the named-theory
    /// contract turns into an explicit error. Compares by well-known NAME: the
    /// goal states the symbol under some name; if the theory has no symbol of
    /// that name (so `symbols.X` is null), it is missing.
    fn missingTheorySymbol(self: *Elaborator, goal: TermId, premises: []const TermId, symbols: presburger_mod.Symbols) ElabError!?[]const u8 {
        const wanted = [_]struct { name: []const u8, present: bool }{
            .{ .name = "succ", .present = symbols.succ != null },
            .{ .name = "add", .present = symbols.add != null },
            .{ .name = "mul", .present = symbols.mul != null },
            .{ .name = "less_than", .present = symbols.less_than != null },
        };
        for (wanted) |w| {
            if (w.present) continue;
            const id = self.interner.intern(w.name) catch return error.OutOfMemory;
            if (self.pool.usesSymNamed(self.env, id, goal)) return w.name;
            for (premises) |p| {
                if (self.pool.usesSymNamed(self.env, id, p)) return w.name;
            }
        }
        return null;
    }

    fn arithmeticJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
        const loc = c.rule.start;
        const premises = try self.resolvePremises(low, block_id, c, "arithmetic");

        // `arithmetic(<theory>)` resolves the arithmetic vocabulary + lemmas
        // against the named theory module's scope (regardless of local
        // aliases); bare `arithmetic` resolves against local scope. Scoped to
        // this call — restored on return.
        const saved_theory = self.theory_file;
        defer self.theory_file = saved_theory;
        if (c.schema) |theory_tok| {
            const ns = try self.internTok(theory_tok);
            self.theory_file = self.env.findNamespace(self.file, ns) orelse
                return self.fail(theory_tok.start, "unknown theory '{s}' (not an imported module)", .{self.text(theory_tok)});
        }

        const symbols = try self.arithmeticSymbols();

        // A NAMED theory is asserted complete: every symbol the goal mentions
        // must be provided, else a hard error naming the gap (rather than a
        // silent opaque-atom countermodel). Bare/local is best-effort.
        if (c.schema) |theory_tok| {
            if (try self.missingTheorySymbol(goal, premises, symbols)) |missing| {
                return self.fail(theory_tok.start, "theory '{s}' lacks symbol '{s}' needed by this goal", .{ self.text(theory_tok), missing });
            }
        }

        // proving 'forall x; F' means proving F with x fixed-but-arbitrary:
        // strip the goal's universal Nat prefix so a mixed body still
        // skeletonizes (a quantifier over a mixed body would be one opaque
        // atom). Binder hints name the variables in countermodels; a hint
        // colliding with an existing free variable gets a hygienic name.
        var stripped = goal;
        if (symbols.nat) |nat_sort| {
            while (true) {
                const node = self.pool.get(stripped);
                if (node != .quant or node.quant.q != .forall or node.quant.sort != nat_sort) break;
                var name = node.quant.hint;
                var collides = self.pool.occursFree(stripped, name);
                for (premises) |p| {
                    if (self.pool.occursFree(p, name)) collides = true;
                }
                if (collides) name = try self.freshNamed(self.interner.str(node.quant.hint));
                const fv = try self.pool.add(.{ .fvar = .{ .name = name, .sort = nat_sort } });
                stripped = try self.pool.open(node.quant.body, fv);
            }
        }

        const verdict = smt_mod.decideMixed(self.arena, self.pool, symbols, premises, stripped) catch return error.OutOfMemory;
        switch (verdict) {
            .valid => {
                // Walk the certifier chain, first-`certified`-wins; collect
                // each link's decline reason for the honest terminal.
                var reasons: [certifiers.len]Reason = undefined;
                for (certifiers, 0..) |link, i| {
                    switch (try link.run(self, low, block_id, goal, c, symbols, loc)) {
                        .certified => |just| return just,
                        .declined => |r| reasons[i] = r,
                    }
                }
                // every link declined: valid but not certifiable here. A
                // `fallback(<thm>)` cites a manual proof (proven) instead; else
                // hard error (default) listing the reasons, or accelerated (--fast).
                if (c.fallback) |fb| return self.arithmeticFallback(fb, goal);
                return self.arithmeticTerminal(loc, &reasons);
            },
            .countermodel => |cm| {
                if (!cm.values_found) {
                    return self.fail(loc, "arithmetic: not a consequence (no small countermodel found)", .{});
                }
                // a relational atom (=, !=, less_than) that is opaque only
                // because it hides a nonlinear term was never decided
                // arithmetically — report that honestly instead of a
                // countermodel that reads as "your true statement is false".
                // (A genuinely propositional opaque atom, like a foreign
                // predicate `p`, is a legitimate part of a mixed countermodel
                // and is left alone.)
                for (cm.opaques) |lit| {
                    if (!self.looksArithmeticRelation(lit.atom, symbols)) continue;
                    if (try presburger_mod.outOfFragment(self.arena, self.pool, symbols, lit.atom)) |offending| {
                        return self.fail(loc, "arithmetic: '{s}' is outside linear arithmetic", .{try self.renderTerm(offending)});
                    }
                }
                if (cm.values.len == 0 and cm.opaques.len == 0) {
                    return self.fail(loc, "arithmetic: the statement is false", .{});
                }
                var msg: std.Io.Writer.Allocating = .init(self.arena);
                var count: usize = 0;
                for (cm.values) |a| {
                    msg.writer.print("{s}{s} := {d}", .{
                        if (count > 0) ", " else "",
                        displayName(self.interner.str(a.name)),
                        a.value,
                    }) catch return error.OutOfMemory;
                    count += 1;
                }
                for (cm.opaques) |lit| {
                    msg.writer.print("{s}{s} := {s}", .{
                        if (count > 0) ", " else "",
                        try self.renderTerm(lit.atom),
                        if (lit.value) "true" else "false",
                    }) catch return error.OutOfMemory;
                    count += 1;
                }
                return self.fail(loc, "arithmetic: false at {s}", .{msg.written()});
            },
            .too_many_atoms => |n| {
                return self.fail(loc, "arithmetic: {d} distinct atoms exceeds the limit of {d}", .{ n, smt_mod.atom_limit });
            },
            .too_large => return self.fail(loc, "arithmetic: decision exceeded the work limit", .{}),
            .overflow => return self.fail(loc, "arithmetic: coefficient overflow", .{}),
        }
    }

    fn checkFreshName(self: *Elaborator, name: StrId, tok: lexer.Token) ElabError!void {
        if (std.mem.indexOfScalar(u8, self.text(tok), '.') != null) {
            return self.fail(tok.start, "declared names cannot be qualified", .{});
        }
        if (self.env.nameTaken(self.file, name)) {
            return self.fail(tok.start, "duplicate declaration of '{s}'", .{self.text(tok)});
        }
    }

    fn resolveSort(self: *Elaborator, tok: lexer.Token) ElabError!SortId {
        const target = try self.resolveTarget(tok);
        return self.env.findSort(target.file, target.base) orelse
            self.fail(tok.start, "unknown sort '{s}'", .{self.text(tok)});
    }

    const Target = struct { file: FileId, base: StrId };

    /// The elaboration context that must follow an AST across files: which
    /// source its tokens index, which file scope resolves its names, and
    /// which file its diagnostics blame.
    const Ctx = struct { source: []const u8, file: FileId, diag: u32 };

    fn swapCtx(self: *Elaborator, ctx: Ctx) Ctx {
        const old: Ctx = .{ .source = self.source, .file = self.file, .diag = self.sink.current_file };
        self.source = ctx.source;
        self.file = ctx.file;
        self.sink.current_file = ctx.diag;
        return old;
    }

    /// Split an (optionally) qualified name: `peano.Nat` resolves the
    /// namespace to its file; a bare name resolves in the current file.
    fn resolveTarget(self: *Elaborator, tok: lexer.Token) ElabError!Target {
        const text_ = self.text(tok);
        const i = std.mem.indexOfScalar(u8, text_, '.') orelse
            return .{ .file = self.file, .base = try self.internTok(tok) };
        const rest = text_[i + 1 ..];
        if (std.mem.indexOfScalar(u8, rest, '.') != null) {
            return self.fail(tok.start, "only one level of namespace qualification is allowed", .{});
        }
        const ns = self.interner.intern(text_[0..i]) catch return error.OutOfMemory;
        const file = self.env.findNamespace(self.file, ns) orelse
            return self.fail(tok.start, "unknown namespace '{s}'", .{text_[0..i]});
        const base = self.interner.intern(rest) catch return error.OutOfMemory;
        return .{ .file = file, .base = base };
    }

    fn resolveParams(self: *Elaborator, params: []const ast.Binder) ElabError!struct { []const SortId, []const StrId } {
        const sorts = try self.arena.alloc(SortId, params.len);
        const names = try self.arena.alloc(StrId, params.len);
        for (params, sorts, names, 0..) |p, *s, *n, i| {
            s.* = try self.resolveSort(p.sort);
            n.* = try self.internTok(p.name);
            try self.checkNoShadow(n.*, p.name);
            for (names[0..i]) |prev| {
                if (prev == n.*) {
                    return self.fail(p.name.start, "duplicate parameter '{s}'", .{self.text(p.name)});
                }
            }
        }
        return .{ sorts, names };
    }

    fn requireProp(self: *Elaborator, typed: Typed, e: *const ast.Expr) ElabError!Typed {
        if (typed.sort != .prop) {
            return self.fail(exprLoc(e), "expected a proposition, got sort '{s}'", .{self.sortName(typed.sort)});
        }
        return typed;
    }

    pub fn exprLoc(e: *const ast.Expr) u32 {
        return switch (e.*) {
            .name => |t| t.start,
            .call => |c| c.callee.start,
            .binary => |b| exprLoc(b.lhs),
            .not => |n| n.tok.start,
            .quant => |q| q.tok.start,
            .lambda => |l| l.tok.start,
        };
    }

    /// No-shadowing rule (checker-enforced): a newly introduced variable or
    /// parameter may not reuse any visible name — a variable in scope, a
    /// schema parameter, or any declared symbol.
    fn checkNoShadow(self: *Elaborator, name: StrId, tok: lexer.Token) ElabError!void {
        for (self.scope.items) |entry| {
            if (entry.name == name) {
                return self.fail(tok.start, "'{s}' shadows a variable in scope; choose a fresh name", .{self.text(tok)});
            }
        }
        if (self.schema_args) |sa| {
            if (sa.contains(name)) {
                return self.fail(tok.start, "'{s}' shadows a schema parameter; choose a fresh name", .{self.text(tok)});
            }
        }
        if (self.env.findSym(self.file, name) != null) {
            return self.fail(tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(tok)});
        }
    }

    fn freshName(self: *Elaborator) ElabError!StrId {
        return self.freshNamed("b");
    }

    /// The name to SHOW for an interned identifier: everything up to the first
    /// `#`. Eigenvariables and other hygienic names carry a `#<n>` disambiguator
    /// (see `bindProofVar` / `freshNamed`); `#` is not a legal identifier
    /// character, so trimming there recovers exactly what the author wrote. Used
    /// by diagnostics that print a bare fvar name outside the `print.zig`
    /// Printer (which strips independently via its own `displayName`).
    fn displayName(interned: []const u8) []const u8 {
        return if (std.mem.indexOfScalar(u8, interned, '#')) |i| interned[0..i] else interned;
    }

    /// hygienic '#'-name with a readable prefix ("simplify#3" in diagnostics,
    /// or a disambiguated eigenvariable "x#7"). The prefix may be an arbitrary
    /// user identifier, so allocate rather than risk truncation.
    fn freshNamed(self: *Elaborator, prefix: []const u8) ElabError!StrId {
        self.fresh_counter += 1;
        const s = std.fmt.allocPrint(self.arena, "{s}#{d}", .{ prefix, self.fresh_counter }) catch return error.OutOfMemory;
        return self.interner.intern(s) catch error.OutOfMemory;
    }

    pub fn elaborateExpr(self: *Elaborator, e: *const ast.Expr) ElabError!Typed {
        switch (e.*) {
            .name => |tok| return self.elaborateName(tok),
            .call => |c| return self.elaborateCall(c),
            .binary => |b| switch (b.op) {
                .implies, .and_op, .or_op => {
                    const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                    const tcc_start = self.pending_tccs.items.len;
                    const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                    // context collection: obligations inside the RHS of an
                    // implication hold under its antecedent; inside the RHS of
                    // a conjunction, under its left conjunct. Disjunction and
                    // negation contribute nothing (conservative).
                    if (b.op == .implies or b.op == .and_op) {
                        for (self.pending_tccs.items[tcc_start..]) |*t| {
                            t.formula = try self.pool.add(.{ .bin = .{
                                .op = .implies,
                                .lhs = lhs.id,
                                .rhs = t.formula,
                            } });
                        }
                    }
                    const op: term.BinOp = switch (b.op) {
                        .implies => .implies,
                        .and_op => .and_op,
                        .or_op => .or_op,
                        else => unreachable,
                    };
                    const id = try self.pool.add(.{ .bin = .{ .op = op, .lhs = lhs.id, .rhs = rhs.id } });
                    return .{ .id = id, .sort = .prop };
                },
                .equal, .not_equal => {
                    const lhs = try self.elaborateExpr(b.lhs);
                    const rhs = try self.elaborateExpr(b.rhs);
                    if (lhs.sort == .prop) {
                        return self.fail(exprLoc(b.lhs), "'=' compares terms, not propositions", .{});
                    }
                    if (rhs.sort != lhs.sort) {
                        return self.fail(exprLoc(b.rhs), "expected sort '{s}', got '{s}'", .{
                            self.sortName(lhs.sort), self.sortName(rhs.sort),
                        });
                    }
                    const eq = try self.pool.add(.{ .eq = .{ .lhs = lhs.id, .rhs = rhs.id } });
                    const id = if (b.op == .not_equal) try self.pool.add(.{ .not = eq }) else eq;
                    return .{ .id = id, .sort = .prop };
                },
            },
            .not => |n| {
                const inner = try self.requireProp(try self.elaborateExpr(n.operand), n.operand);
                const id = try self.pool.add(.{ .not = inner.id });
                return .{ .id = id, .sort = .prop };
            },
            .quant => |q| {
                // binders become fresh fvars so every intermediate term stays
                // locally closed (capture-proof schema substitution depends on
                // this); the fvars are closed into de Bruijn form right here
                const sort = try self.resolveSort(q.binders[0].sort);
                const fresh = try self.arena.alloc(StrId, q.binders.len);
                for (q.binders, fresh) |b, *fr| {
                    const bname = try self.internTok(b.name);
                    try self.checkNoShadow(bname, b.name);
                    fr.* = try self.freshName();
                    try self.scope.append(self.arena, .{
                        .name = bname,
                        .sort = sort,
                        .fvar = fr.*,
                    });
                }
                const tcc_start = self.pending_tccs.items.len;
                const body = try self.requireProp(try self.elaborateExpr(q.body), q.body);
                // close innermost binder first
                var id = body.id;
                var i = q.binders.len;
                while (i > 0) {
                    i -= 1;
                    id = try self.pool.close(id, fresh[i]);
                    id = try self.pool.add(.{ .quant = .{
                        .q = if (q.q == .forall) .forall else .exists,
                        .sort = sort,
                        .hint = try self.internTok(q.binders[i].name),
                        .body = id,
                    } });
                    // obligations under a binder are universally closed over it
                    for (self.pending_tccs.items[tcc_start..]) |*t| {
                        const closed = try self.pool.close(t.formula, fresh[i]);
                        t.formula = try self.pool.add(.{ .quant = .{
                            .q = .forall,
                            .sort = sort,
                            .hint = try self.internTok(q.binders[i].name),
                            .body = closed,
                        } });
                    }
                    _ = self.scope.pop();
                }
                return .{ .id = id, .sort = .prop };
            },
            .lambda => |l| {
                return self.fail(l.tok.start, "lambda literals are only valid as schema arguments", .{});
            },
        }
    }

    fn elaborateName(self: *Elaborator, tok: lexer.Token) ElabError!Typed {
        // qualified names bypass locals entirely (locals are never qualified)
        if (std.mem.indexOfScalar(u8, self.text(tok), '.') != null) {
            const target = try self.resolveTarget(tok);
            return self.elaborateSymRef(tok, target);
        }
        const name = try self.internTok(tok);
        // scope lookup, innermost first (locals shadow schema params)
        var i = self.scope.items.len;
        while (i > 0) {
            i -= 1;
            const entry = self.scope.items[i];
            if (entry.name == name) {
                const id = try self.pool.add(.{ .fvar = .{ .name = entry.fvar, .sort = entry.sort } });
                return .{ .id = id, .sort = entry.sort };
            }
        }
        // schema parameter (only while elaborating a schema body/proof)
        if (self.schema_args) |sa| {
            if (sa.get(name)) |arg| switch (arg) {
                .value => |v| return v,
                .lambda => return self.fail(tok.start, "schema parameter '{s}' requires an argument", .{self.text(tok)}),
            };
        }
        return self.elaborateSymRef(tok, .{ .file = self.file, .base = name });
    }

    /// 0-ary symbol reference (possibly namespace-qualified)
    fn elaborateSymRef(self: *Elaborator, tok: lexer.Token, target: Target) ElabError!Typed {
        if (self.env.findSym(target.file, target.base)) |sym_id| {
            const sym = self.env.sym(sym_id);
            if (sym.arg_sorts.len != 0) {
                return self.fail(tok.start, "'{s}' expects {d} argument(s), got 0", .{ self.text(tok), sym.arg_sorts.len });
            }
            // a define is transparent: every use IS its term
            if (sym.definition) |def| {
                return .{ .id = def, .sort = sym.result };
            }
            const id = try self.pool.addApp(if (sym.kind == .pred) .pred else .app, sym_id, &.{});
            return .{ .id = id, .sort = sym.result };
        }
        return self.fail(tok.start, "unknown identifier '{s}'", .{self.text(tok)});
    }

    fn elaborateCall(self: *Elaborator, c: ast.Expr.Call) ElabError!Typed {
        const target = try self.resolveTarget(c.callee);
        const name = target.base;
        // schema parameter application: beta-reduce at the term level
        // (schema params are never qualified, but a stray hit is harmless:
        // qualified callee text never equals a bare param name)
        if (self.schema_args) |sa| {
            if (sa.get(name)) |arg| switch (arg) {
                .lambda => |l| {
                    if (c.args.len != 1) {
                        return self.fail(c.callee.start, "schema parameter '{s}' expects 1 argument, got {d}", .{ self.text(c.callee), c.args.len });
                    }
                    const t = try self.elaborateExpr(c.args[0]);
                    if (t.sort != l.arg_sort) {
                        return self.fail(exprLoc(c.args[0]), "expected sort '{s}', got '{s}'", .{
                            self.sortName(l.arg_sort), self.sortName(t.sort),
                        });
                    }
                    return .{ .id = try self.pool.open(l.body, t.id), .sort = l.result_sort };
                },
                .value => return self.fail(c.callee.start, "schema parameter '{s}' takes no arguments", .{self.text(c.callee)}),
            };
        }
        const sym_id = self.env.findSym(target.file, name) orelse {
            return self.fail(c.callee.start, "unknown identifier '{s}'", .{self.text(c.callee)});
        };
        const sym = self.env.sym(sym_id);
        if (sym.arg_sorts.len != c.args.len) {
            return self.fail(c.callee.start, "'{s}' expects {d} argument(s), got {d}", .{
                self.text(c.callee), sym.arg_sorts.len, c.args.len,
            });
        }
        const arg_ids = try self.arena.alloc(TermId, c.args.len);
        for (c.args, sym.arg_sorts, arg_ids) |arg, expected, *out| {
            const typed = try self.elaborateExpr(arg);
            if (typed.sort != expected) {
                return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{
                    self.sortName(expected), self.sortName(typed.sort),
                });
            }
            out.* = typed.id;
        }
        // guarded application: owe the guard at the actual arguments.
        // Emitted AFTER the args are elaborated, so inner obligations of
        // nested guarded applications precede outer ones.
        if (sym.guard) |guard| {
            // simultaneous substitution via fresh intermediates: a user
            // variable spelled like a later param must not be re-substituted
            var g = guard;
            const fresh = try self.arena.alloc(StrId, sym.param_names.len);
            for (sym.param_names, fresh) |pn, *fr| {
                fr.* = try self.freshName();
                // placeholder fvar; its sort is irrelevant (replaced below)
                const fv = try self.pool.add(.{ .fvar = .{ .name = fr.*, .sort = .prop } });
                g = try self.pool.substFvar(g, pn, fv);
            }
            for (fresh, arg_ids) |fr, actual| {
                g = try self.pool.substFvar(g, fr, actual);
            }
            try self.pending_tccs.append(self.arena, .{ .formula = g, .loc = c.callee.start });
        }
        const id = try self.pool.addApp(if (sym.kind == .pred) .pred else .app, sym_id, arg_ids);
        return .{ .id = id, .sort = sym.result };
    }
};

// --- tests ---

const testing = std.testing;
const parser_mod = @import("parser.zig");

pub const TestCtx = struct {
    arena_state: *std.heap.ArenaAllocator,
    interner: *intern.Interner,
    pool: *term.Pool,
    env: *Env,
    sink: *Diagnostics.Sink,
    file: ast.File,
    source: []const u8,

    pub fn run(gpa: Allocator, source: []const u8) !TestCtx {
        const arena_state = try gpa.create(std.heap.ArenaAllocator);
        arena_state.* = .init(gpa);
        const arena = arena_state.allocator();

        const interner = try arena.create(intern.Interner);
        interner.* = .init(arena);
        const pool = try arena.create(term.Pool);
        pool.* = .init(arena);
        const sink = try arena.create(Diagnostics.Sink);
        sink.* = .init(arena);
        const env = try arena.create(Env);
        env.* = try .init(arena, interner);
        const file_id = try env.newFile();

        var p: parser_mod.Parser = .init(arena, source, sink);
        const file = try p.parseFile();
        var elab: Elaborator = .init(arena, source, interner, pool, env, sink, file_id);
        try elab.elaborateFile(file);
        return .{
            .arena_state = arena_state,
            .interner = interner,
            .pool = pool,
            .env = env,
            .sink = sink,
            .file = file,
            .source = source,
        };
    }

    pub fn deinit(self: *TestCtx, gpa: Allocator) void {
        self.arena_state.deinit();
        gpa.destroy(self.arena_state);
    }

    pub fn firstMessage(self: *const TestCtx) []const u8 {
        return self.sink.list.items[0].message;
    }
};

test "well-sorted declarations elaborate cleanly" {
    const source =
        \\sort Nat
        \\const ZERO: Nat
        \\func succ(n: Nat): Nat
        \\func div(a: Nat, b: Nat): Nat requires b != ZERO
        \\pred even(n: Nat)
        \\axiom evenZero: even(ZERO)
        \\axiom addForm: forall a, b: Nat; exists c: Nat; succ(a) = c
        \\axiom induction(prop: Nat -> Prop):
        \\  prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)
    ;
    var ctx = try TestCtx.run(testing.allocator, source);
    defer ctx.deinit(testing.allocator);
    try testing.expectEqual(0, ctx.sink.list.items.len);

    // div stored its guard: not (eq (fvar b) ZERO)
    const div = ctx.env.sym(ctx.env.findSym(@enumFromInt(0), try ctx.interner.intern("div")).?);
    const guard = ctx.pool.get(div.guard.?);
    try testing.expect(guard == .not);
    // schema stored lazily as a form
    const ind = ctx.env.findStatement(@enumFromInt(0), try ctx.interner.intern("induction")).?;
    try testing.expect(ind.* == .schema);
}

test "sort errors are precise" {
    const cases = [_]struct { src: []const u8, msg: []const u8 }{
        .{ .src = "sort Nat\nfunc succ(n: Nat): Nat\npred p\naxiom bad: succ(p) = succ(p)", .msg = "expected sort 'Nat', got 'Prop'" },
        .{ .src = "sort Nat\nconst ZERO: Nat\naxiom bad: ZERO", .msg = "expected a proposition, got sort 'Nat'" },
        .{ .src = "sort Nat\naxiom bad: missing = missing", .msg = "unknown identifier 'missing'" },
        .{ .src = "sort Nat\nfunc succ(n: Nat): Nat\nconst ZERO: Nat\naxiom bad: succ(ZERO, ZERO) = ZERO", .msg = "'succ' expects 1 argument(s), got 2" },
        .{ .src = "pred p\npred q\naxiom bad: p = q", .msg = "'=' compares terms, not propositions" },
        .{ .src = "sort Nat\nsort Nat", .msg = "duplicate declaration of 'Nat'" },
        .{ .src = "const ZERO: natt", .msg = "unknown sort 'natt'" },
        .{ .src = "sort Nat\nfunc bad(n: Nat): Prop", .msg = "a func cannot return 'Prop'; declare a pred instead" },
        .{ .src = "sort Nat\naxiom bad: forall x: Nat; fun k: Nat => k = x", .msg = "lambda literals are only valid as schema arguments" },
        // guards must be guard-free (no obligation regress)
        .{ .src = "sort Nat\nconst ZERO: Nat\nfunc div(a: Nat, b: Nat): Nat requires b != ZERO\nfunc f(a: Nat): Nat requires div(a, a) = a", .msg = "a 'requires' clause may only mention total functions" },
        // disjunction contributes NO context to obligations (conservative):
        // the guard must hold outright even under p \/ ...
        .{ .src = "sort Nat\nconst ZERO: Nat\nfunc div(a: Nat, b: Nat): Nat requires b != ZERO\npred p\naxiom a1: p or div(ZERO, ZERO) = ZERO", .msg = "unproved obligation: 'ZERO != ZERO'" },
        // no-shadowing: nothing shadows anything
        .{ .src = "sort Nat\nconst ZERO: Nat\naxiom bad: forall ZERO: Nat; ZERO = ZERO", .msg = "'ZERO' shadows a declaration; choose a fresh name" },
        .{ .src = "sort Nat\naxiom bad: forall a: Nat; forall a: Nat; a = a", .msg = "'a' shadows a variable in scope; choose a fresh name" },
        .{ .src = "sort Nat\nfunc succ(n: Nat): Nat\nfunc bad(succ: Nat): Nat", .msg = "'succ' shadows a declaration; choose a fresh name" },
    };
    for (cases) |case| {
        var ctx = try TestCtx.run(testing.allocator, case.src);
        defer ctx.deinit(testing.allocator);
        try testing.expectEqual(1, ctx.sink.list.items.len);
        try testing.expectEqualStrings(case.msg, ctx.firstMessage());
    }
}

test "de Bruijn indices correct under nested binders" {
    const source =
        \\sort Nat
        \\const ZERO: Nat
        \\func add(a: Nat, b: Nat): Nat
        \\axiom nested: forall a: Nat; forall b: Nat; add(a, b) = add(b, a)
    ;
    var ctx = try TestCtx.run(testing.allocator, source);
    defer ctx.deinit(testing.allocator);
    try testing.expectEqual(0, ctx.sink.list.items.len);

    // nested: add(a, b) under two binders = app(bvar1, bvar0)
    const nested = ctx.env.findStatement(@enumFromInt(0), try ctx.interner.intern("nested")).?.axiom;
    const q1 = ctx.pool.get(nested.formula).quant;
    const q2 = ctx.pool.get(q1.body).quant;
    const neq = ctx.pool.get(q2.body).eq;
    const lhs_app = ctx.pool.get(neq.lhs).app;
    try testing.expectEqual(term.Node{ .bvar = 1 }, ctx.pool.get(ctx.pool.args(lhs_app)[0]));
    try testing.expectEqual(term.Node{ .bvar = 0 }, ctx.pool.get(ctx.pool.args(lhs_app)[1]));
}
