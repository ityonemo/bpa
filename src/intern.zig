//! String interner: identifiers become u32 ids; equality is integer compare.

const std = @import("std");

pub const StrId = enum(u32) { _ };

pub const Interner = struct {
    arena: std.mem.Allocator,
    map: std.StringHashMapUnmanaged(StrId) = .empty,
    strings: std.ArrayList([]const u8) = .empty,

    pub fn init(arena: std.mem.Allocator) Interner {
        return .{ .arena = arena };
    }

    pub fn intern(self: *Interner, s: []const u8) !StrId {
        const gop = try self.map.getOrPut(self.arena, s);
        if (!gop.found_existing) {
            const id: StrId = @enumFromInt(self.strings.items.len);
            // key must outlive the caller's buffer
            const copy = try self.arena.dupe(u8, s);
            gop.key_ptr.* = copy;
            gop.value_ptr.* = id;
            try self.strings.append(self.arena, copy);
        }
        return gop.value_ptr.*;
    }

    pub fn str(self: *const Interner, id: StrId) []const u8 {
        return self.strings.items[@intFromEnum(id)];
    }
};

test "interning dedupes and round-trips" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var interner: Interner = .init(arena_state.allocator());

    const a = try interner.intern("add");
    const b = try interner.intern("zero");
    const a2 = try interner.intern("add");
    try std.testing.expectEqual(a, a2);
    try std.testing.expect(a != b);
    try std.testing.expectEqualStrings("add", interner.str(a));
    try std.testing.expectEqualStrings("zero", interner.str(b));
}
