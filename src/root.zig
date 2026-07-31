//! bpa core library. All proof-checking logic is exposed from here;
//! src/main.zig is a thin CLI wrapper.

const std = @import("std");

pub const lexer = @import("lexer.zig");
pub const ast = @import("ast.zig");
pub const parser = @import("parser.zig");
pub const diagnostics = @import("diagnostics.zig");
pub const intern = @import("intern.zig");
pub const term = @import("term.zig");
pub const env = @import("env.zig");
pub const elaborate = @import("elaborate.zig");
pub const Verify = elaborate.Verify;
pub const print = @import("print.zig");
pub const kernel = @import("kernel.zig");
pub const fmt = @import("fmt.zig");
pub const literate = @import("literate.zig");
pub const simplify = @import("simplify.zig");
pub const smt = @import("smt.zig");
pub const presburger = @import("presburger.zig");
pub const farkas = @import("farkas.zig");

pub const query = struct {
    pub const outline = @import("query/outline.zig");
    pub const theorem = @import("query/theorem.zig");
    pub const whereis = @import("query/whereis.zig");
    pub const search = @import("query/search.zig");
    pub const uses = @import("query/uses.zig");
    pub const oracles = @import("query/oracles.zig");
};

pub const CheckResult = struct {
    file: ast.File,
    sink: *diagnostics.Sink,
    declarations: usize,
    theorems_proven: usize,

    pub fn ok(self: *const CheckResult) bool {
        return self.sink.list.items.len == 0;
    }
};

/// Check a .bpa source. All allocations go into `arena`; diagnostics are
/// collected in the result's sink (rendered by the caller).
pub fn checkSource(arena: std.mem.Allocator, source: []const u8) !CheckResult {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);

    var p: parser.Parser = .init(arena, source, sink);
    const file = try p.parseFile();

    const interner = try arena.create(intern.Interner);
    interner.* = .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);
    const environment = try arena.create(env.Env);
    environment.* = try .init(arena, interner);
    const file_id = try environment.newFile();

    var elab: elaborate.Elaborator = .init(arena, source, interner, pool, environment, sink, file_id);
    try elab.elaborateFile(file);

    var proven: usize = 0;
    for (environment.statements.items) |stmt| {
        if (stmt == .theorem and stmt.theorem.proven) proven += 1;
    }
    return .{
        .file = file,
        .sink = sink,
        .declarations = file.decls.len,
        .theorems_proven = proven,
    };
}

// --- multi-file checking (imports) ---

pub const ReadFileFn = *const fn (ctx: ?*anyopaque, arena: std.mem.Allocator, path: []const u8) anyerror![]const u8;

pub const ProjectResult = struct {
    files: []const diagnostics.FileSrc,
    sink: *diagnostics.Sink,
    declarations: usize,
    theorems_proven: usize,
    theorems_trusted: usize,
    /// proven theorems split by taint: pure + tainted = proven
    theorems_pure: usize,
    theorems_tainted: usize,
    /// distinct oracle names across tainted theorems, first-use order
    oracle_names: []const []const u8,

    pub fn ok(self: *const ProjectResult) bool {
        return self.sink.list.items.len == 0;
    }
};

const Loader = struct {
    arena: std.mem.Allocator,
    sink: *diagnostics.Sink,
    interner: *intern.Interner,
    pool: *term.Pool,
    environment: *env.Env,
    files: std.ArrayList(diagnostics.FileSrc) = .empty,
    /// resolved path -> load state (null while loading: cycle detection)
    by_path: std.StringHashMapUnmanaged(?env.FileId) = .empty,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    /// which verification layers are active (see elaborate.Verify). When
    /// `recheck_imports` is false, imported files are TRUSTED: declarations
    /// load, proofs are not re-checked.
    verify: elaborate.Verify,
    /// the standard library root: import paths beginning "std/" resolve here
    /// (the prefix is reserved) instead of relative to the importing file
    std_root: []const u8,
    declarations: usize = 0,

    /// Load, (maybe) check, and register one file. Imports are processed
    /// depth-first, so a file's dependencies are fully elaborated before the
    /// file itself (its qualified names resolve into their scopes).
    fn load(self: *Loader, path: []const u8, source: []const u8, is_root: bool) !env.FileId {
        const gop = try self.by_path.getOrPut(self.arena, path);
        if (gop.found_existing) unreachable; // caller checks before descending
        gop.value_ptr.* = null; // loading: a re-visit is a cycle

        const file_id = try self.environment.newFile();
        std.debug.assert(@intFromEnum(file_id) == self.files.items.len);
        try self.files.append(self.arena, .{ .path = path, .source = source });

        self.sink.current_file = @intFromEnum(file_id);
        var p: parser.Parser = .init(self.arena, source, self.sink);
        const parsed = try p.parseFile();
        self.declarations += parsed.decls.len;

        // resolve imports (recursing), building raw-path -> FileId
        var import_map: std.AutoHashMapUnmanaged(intern.StrId, env.FileId) = .empty;
        for (parsed.decls) |decl| {
            if (decl != .import) continue;
            const d = decl.import;
            const raw_quoted = source[d.path.start..d.path.end];
            const raw = raw_quoted[1 .. raw_quoted.len - 1];
            const resolved = if (std.mem.startsWith(u8, raw, "std/"))
                try std.fs.path.resolve(self.arena, &.{ self.std_root, raw["std/".len..] })
            else
                try std.fs.path.resolve(self.arena, &.{ std.fs.path.dirname(path) orelse ".", raw });

            const child: ?env.FileId = child: {
                if (self.by_path.get(resolved)) |state| {
                    break :child state orelse {
                        self.sink.current_file = @intFromEnum(file_id);
                        try self.sink.add(d.path.start, "import cycle detected via '{s}'", .{resolved});
                        break :child null;
                    };
                }
                const src = self.read_fn(self.read_ctx, self.arena, resolved) catch {
                    self.sink.current_file = @intFromEnum(file_id);
                    try self.sink.add(d.path.start, "cannot open '{s}': file not found", .{resolved});
                    break :child null;
                };
                break :child try self.load(resolved, src, false);
            };
            if (child) |c| {
                const raw_id = try self.interner.intern(raw);
                try import_map.put(self.arena, raw_id, c);
            }
        }

        self.sink.current_file = @intFromEnum(file_id);
        var elab: elaborate.Elaborator = .init(self.arena, source, self.interner, self.pool, self.environment, self.sink, file_id);
        elab.imports = &import_map;
        elab.trusted = !is_root and !self.verify.recheck_imports;
        elab.verify = self.verify;
        try elab.elaborateFile(parsed);

        self.by_path.getPtr(path).?.* = file_id;
        return file_id;
    }
};

/// Check a root file and everything it imports. `verify` selects which layers
/// are actually verified (default: everything). When `verify.recheck_imports`
/// is false, imported files contribute their declarations but their proofs are
/// TRUSTED, not re-checked.
pub fn checkProject(
    arena: std.mem.Allocator,
    root_path: []const u8,
    root_source: []const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    verify: elaborate.Verify,
    std_root: []const u8,
) !ProjectResult {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);
    const interner = try arena.create(intern.Interner);
    interner.* = .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);
    const environment = try arena.create(env.Env);
    environment.* = try .init(arena, interner);

    var loader: Loader = .{
        .arena = arena,
        .sink = sink,
        .interner = interner,
        .pool = pool,
        .environment = environment,
        .read_ctx = read_ctx,
        .read_fn = read_fn,
        .verify = verify,
        .std_root = std_root,
    };
    const canonical_root = try std.fs.path.resolve(arena, &.{root_path});
    _ = try loader.load(canonical_root, root_source, true);

    var proven: usize = 0;
    var trusted: usize = 0;
    var pure_count: usize = 0;
    var tainted: usize = 0;
    var oracle_names: std.ArrayList([]const u8) = .empty;
    for (environment.statements.items) |stmt| {
        if (stmt != .theorem) continue;
        if (stmt.theorem.trusted) {
            trusted += 1;
        } else if (stmt.theorem.proven) {
            proven += 1;
            if (stmt.theorem.oracles.len == 0) {
                pure_count += 1;
            } else {
                tainted += 1;
                outer: for (stmt.theorem.oracles) |o| {
                    const s = interner.str(o);
                    for (oracle_names.items) |seen| {
                        if (std.mem.eql(u8, seen, s)) continue :outer;
                    }
                    try oracle_names.append(arena, s);
                }
            }
        }
    }
    return .{
        .files = loader.files.items,
        .sink = sink,
        .declarations = loader.declarations,
        .theorems_proven = proven,
        .theorems_trusted = trusted,
        .theorems_pure = pure_count,
        .theorems_tainted = tainted,
        .oracle_names = oracle_names.items,
    };
}

test {
    std.testing.refAllDecls(@This());
    std.testing.refAllDecls(query.outline);
    std.testing.refAllDecls(query.theorem);
    std.testing.refAllDecls(query.whereis);
    std.testing.refAllDecls(query.search);
    std.testing.refAllDecls(query.uses);
    std.testing.refAllDecls(query.oracles);
    std.testing.refAllDecls(literate);
}
