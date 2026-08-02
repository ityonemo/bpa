//! The environment: entities (sorts, symbols, statements) are GLOBAL across
//! all loaded files — ids are meaningful everywhere, which is what makes
//! aliases views rather than copies. NAME RESOLUTION is per-file: each file
//! has its own scope mapping names to entity ids, plus its imported
//! namespaces. An alias just registers an existing entity id under a local
//! name.

const std = @import("std");
const Allocator = std.mem.Allocator;
const intern = @import("intern.zig");
const StrId = intern.StrId;
const term = @import("term.zig");
const SortId = term.SortId;
const SymId = term.SymId;
const TermId = term.TermId;
const ast = @import("ast.zig");

pub const FileId = enum(u32) { _ };

pub const Symbol = struct {
    name: StrId,
    kind: term.AppKind, // .app: func/const; .pred: predicate
    arg_sorts: []const SortId,
    /// result sort; for predicates always .prop
    result: SortId,
    /// `requires` clause, elaborated with params as fvars (by param name)
    guard: ?TermId,
    /// `define`d symbols: the term every use transparently expands to
    /// (the kernel never sees the symbol itself)
    definition: ?TermId = null,
    /// param names, needed to substitute actuals into the guard
    param_names: []const StrId,
    loc: u32,
};

pub const StatementId = enum(u32) { _ };

pub const Statement = union(enum) {
    axiom: Fact,
    theorem: Fact,
    /// stored form: NOT elaborated until instantiated (comptime semantics)
    schema: Schema,

    pub const Fact = struct {
        name: StrId,
        formula: TermId,
        loc: u32,
        proven: bool = true,
        /// proven-by-trust: an imported theorem whose proof was NOT checked
        /// (no --recursive). Reported separately in the summary.
        trusted: bool = false,
        /// accelerated-tactic names this proof leaned on, transitively through
        /// citations (empty = every step kernel-checked). Disclosed in the summary; rejected
        /// by --pure.
        accelerated: []const StrId = &.{},
    };
    pub const Schema = struct {
        name: StrId,
        params: []const ast.SchemaParam,
        body: *const ast.Expr,
        /// proof steps for a theorem-schema; re-elaborated per instantiation
        proof: ?[]const ast.Step,
        /// the defining file: its scope resolves the body/proof, and its
        /// source carries the diagnostics
        file: FileId,
        /// the defining file's source — the stored AST's tokens index into it
        source: []const u8,
        loc: u32,
    };
};

pub const FileScope = struct {
    sort_names: std.AutoHashMapUnmanaged(StrId, SortId) = .empty,
    sym_names: std.AutoHashMapUnmanaged(StrId, SymId) = .empty,
    statement_names: std.AutoHashMapUnmanaged(StrId, StatementId) = .empty,
    namespaces: std.AutoHashMapUnmanaged(StrId, FileId) = .empty,
};

pub const Env = struct {
    arena: Allocator,
    sorts: std.ArrayList(struct { name: StrId, loc: u32 }) = .empty,
    syms: std.ArrayList(Symbol) = .empty,
    statements: std.ArrayList(Statement) = .empty,
    scopes: std.ArrayList(FileScope) = .empty,
    prop_name: StrId,

    /// Creates the builtin `Prop` sort entity (SortId 0). Files are added
    /// with `newFile`, each seeing `Prop` under its own scope.
    pub fn init(arena: Allocator, interner: *intern.Interner) !Env {
        var env: Env = .{ .arena = arena, .prop_name = try interner.intern("Prop") };
        try env.sorts.append(arena, .{ .name = env.prop_name, .loc = 0 });
        return env;
    }

    pub fn newFile(self: *Env) !FileId {
        const id: FileId = @enumFromInt(self.scopes.items.len);
        try self.scopes.append(self.arena, .{});
        try self.scopes.items[@intFromEnum(id)].sort_names.put(self.arena, self.prop_name, .prop);
        return id;
    }

    fn scope(self: *Env, file: FileId) *FileScope {
        return &self.scopes.items[@intFromEnum(file)];
    }

    // --- entity accessors (file-independent) ---

    pub fn sym(self: *const Env, id: SymId) Symbol {
        return self.syms.items[@intFromEnum(id)];
    }

    pub fn sortName(self: *const Env, interner: *const intern.Interner, id: SortId) []const u8 {
        return interner.str(self.sorts.items[@intFromEnum(id)].name);
    }

    // --- declaration (create entity + bind name in the declaring file) ---

    pub fn addSort(self: *Env, file: FileId, name: StrId, loc: u32) !SortId {
        const id: SortId = @enumFromInt(self.sorts.items.len);
        try self.sorts.append(self.arena, .{ .name = name, .loc = loc });
        try self.scope(file).sort_names.put(self.arena, name, id);
        return id;
    }

    pub fn addSym(self: *Env, file: FileId, symbol: Symbol) !SymId {
        const id: SymId = @enumFromInt(self.syms.items.len);
        try self.syms.append(self.arena, symbol);
        try self.scope(file).sym_names.put(self.arena, symbol.name, id);
        return id;
    }

    pub fn addStatement(self: *Env, file: FileId, name: StrId, stmt: Statement) !StatementId {
        const id: StatementId = @enumFromInt(self.statements.items.len);
        try self.statements.append(self.arena, stmt);
        try self.scope(file).statement_names.put(self.arena, name, id);
        return id;
    }

    pub fn addNamespace(self: *Env, file: FileId, name: StrId, target: FileId) !void {
        try self.scope(file).namespaces.put(self.arena, name, target);
    }

    // --- aliasing (bind an EXISTING entity under a local name) ---

    pub fn registerSort(self: *Env, file: FileId, name: StrId, id: SortId) !void {
        try self.scope(file).sort_names.put(self.arena, name, id);
    }

    pub fn registerSym(self: *Env, file: FileId, name: StrId, id: SymId) !void {
        try self.scope(file).sym_names.put(self.arena, name, id);
    }

    pub fn registerStatement(self: *Env, file: FileId, name: StrId, id: StatementId) !void {
        try self.scope(file).statement_names.put(self.arena, name, id);
    }

    // --- per-file resolution ---

    pub fn findSort(self: *Env, file: FileId, name: StrId) ?SortId {
        return self.scope(file).sort_names.get(name);
    }

    pub fn findSym(self: *Env, file: FileId, name: StrId) ?SymId {
        return self.scope(file).sym_names.get(name);
    }

    pub fn findStatementId(self: *Env, file: FileId, name: StrId) ?StatementId {
        return self.scope(file).statement_names.get(name);
    }

    pub fn findStatement(self: *Env, file: FileId, name: StrId) ?*Statement {
        const id = self.findStatementId(file, name) orelse return null;
        return &self.statements.items[@intFromEnum(id)];
    }

    pub fn findNamespace(self: *Env, file: FileId, name: StrId) ?FileId {
        return self.scope(file).namespaces.get(name);
    }

    pub fn nameTaken(self: *Env, file: FileId, name: StrId) bool {
        const s = self.scope(file);
        return s.sort_names.contains(name) or s.sym_names.contains(name) or
            s.statement_names.contains(name) or s.namespaces.contains(name);
    }
};
