//! Surface AST for .bpa files. Arena-allocated tree; nodes reference source
//! tokens for diagnostics. Terms and formulas share one Expr type — the
//! elaborator sorts them out by sort. Lambdas exist only here, never in
//! kernel terms.

const std = @import("std");
const Token = @import("lexer.zig").Token;

pub const Binder = struct { name: Token, sort: Token };

/// Schema parameter, e.g. `P: nat -> prop`. arg_sorts empty = plain value param.
pub const SchemaParam = struct { name: Token, arg_sorts: []const Token, result: Token };

pub const Expr = union(enum) {
    name: Token,
    call: Call,
    binary: Binary,
    not: Not,
    quant: Quant,
    lambda: Lambda,

    pub const Call = struct { callee: Token, args: []const *const Expr };
    pub const BinOp = enum { implies, and_op, or_op, equal, not_equal };
    pub const Binary = struct {
        op: BinOp,
        tok: Token,
        lhs: *const Expr,
        rhs: *const Expr,
        /// set when this node was wrapped in explicit parentheses in the
        /// source. Used only to enforce the mixed-boolean-operator paren rule
        /// during parsing; ignored everywhere else.
        paren: bool = false,
    };
    pub const Not = struct {
        tok: Token,
        operand: *const Expr,
        /// see Binary.paren
        paren: bool = false,
    };
    pub const Quant = struct {
        q: enum { forall, exists },
        tok: Token,
        binders: []const Binder,
        body: *const Expr,
    };
    pub const Lambda = struct { tok: Token, binders: []const Binder, body: *const Expr };
};

pub const Step = struct {
    label: Token,
    body: Body,

    pub const Body = union(enum) {
        claim: Claim,
        assume: Block,
        fix: FixBlock,
        unpack: UnpackBlock,
        case: CaseBlock,
    };
    pub const Claim = struct {
        formula: *const Expr,
        rule: Token,
        /// schema name, only when rule is `instantiate`
        schema: ?Token,
        args: []const *const Expr,
        refs: []const Token,
        /// `arithmetic ... fallback(<thm>)`: a manually-proven theorem to cite
        /// as the certificate when the certifier chain declines (instead of the
        /// hard error). Keeps the step pure. Arithmetic-only for now.
        fallback: ?Token = null,
    };
    pub const Block = struct { formula: *const Expr, steps: []const Step };
    pub const FixBlock = struct { name: Token, sort: Token, steps: []const Step };
    pub const UnpackBlock = struct { name: Token, sort: Token, from: Token, steps: []const Step };
    /// `case on disj { arm* }` — eliminate the disjunction proved by step
    /// `disj`, one `arm` per (left-nested) disjunct, all arms concluding the
    /// step's goal. Sugar for a hand-written (nested) `or_elim`.
    pub const CaseBlock = struct {
        /// the shared goal every arm concludes (stated on the step line)
        goal: *const Expr,
        disj: Token,
        arms: []const Arm,
        /// one arm: `label| assume <disjunct> { steps }`
        pub const Arm = struct { label: Token, assumption: *const Expr, steps: []const Step };
    };
};

pub const AliasKind = enum { sort, constant, func, pred, axiom, theorem };

pub const Decl = union(enum) {
    /// `import ns <<< "path.bpa"` — binds a namespace to a loaded file
    import: struct { ns: Token, path: Token },
    /// `forward name` — a manifest entry: promises `name` is defined later in
    /// this file as a theorem (checked at end of file; nothing else)
    forward: struct { name: Token },
    /// `sort Nat = peano.Nat` etc — a local name for an imported entity
    alias: struct { kind: AliasKind, name: Token, target: Token },
    sort: struct { name: Token },
    constant: struct { name: Token, sort: Token },
    /// `define NAME = expr` — a transparent abbreviation: every use expands
    /// to the term at elaboration; the kernel never sees the name
    define: struct { name: Token, value: *const Expr },
    func: struct { name: Token, params: []const Binder, result: Token, requires: ?*const Expr },
    pred: struct { name: Token, params: []const Binder },
    axiom: struct { name: Token, formula: *const Expr },
    schema: struct {
        name: Token,
        params: []const SchemaParam,
        formula: *const Expr,
        /// proof-carrying schema: re-checked per instantiation (never at decl)
        steps: ?[]const Step,
    },
    theorem: struct { name: Token, formula: *const Expr, steps: []const Step },
};

pub const File = struct { decls: []const Decl };

/// Debug/test dump of an Expr as an s-expression. Identifier text comes from source.
pub fn dumpExpr(w: *std.Io.Writer, source: []const u8, e: *const Expr) std.Io.Writer.Error!void {
    switch (e.*) {
        .name => |t| try w.writeAll(source[t.start..t.end]),
        .call => |c| {
            try w.print("({s}", .{source[c.callee.start..c.callee.end]});
            for (c.args) |a| {
                try w.writeAll(" ");
                try dumpExpr(w, source, a);
            }
            try w.writeAll(")");
        },
        .binary => |b| {
            try w.print("({t} ", .{b.op});
            try dumpExpr(w, source, b.lhs);
            try w.writeAll(" ");
            try dumpExpr(w, source, b.rhs);
            try w.writeAll(")");
        },
        .not => |n| {
            try w.writeAll("(not ");
            try dumpExpr(w, source, n.operand);
            try w.writeAll(")");
        },
        .quant => |q| {
            try w.print("({t}", .{q.q});
            for (q.binders) |b| try w.print(" {s}:{s}", .{
                source[b.name.start..b.name.end],
                source[b.sort.start..b.sort.end],
            });
            try w.writeAll(" ");
            try dumpExpr(w, source, q.body);
            try w.writeAll(")");
        },
        .lambda => |l| {
            try w.writeAll("(fun");
            for (l.binders) |b| try w.print(" {s}:{s}", .{
                source[b.name.start..b.name.end],
                source[b.sort.start..b.sort.end],
            });
            try w.writeAll(" ");
            try dumpExpr(w, source, l.body);
            try w.writeAll(")");
        },
    }
}
