//! Literate bpa: `bpa check foo.md` checks the proofs embedded in a Markdown
//! document. Only ```` ```bpa ```` fenced blocks are code; everything else is
//! prose.
//!
//! The extraction is a MASK, not a copy: every line outside a `bpa` block —
//! prose, blank lines, the fence lines themselves — is replaced by an empty
//! line, and the *contents* of `bpa` blocks are kept verbatim in place. So the
//! result has the SAME byte and line offsets as the original `.md`, which means
//! error locations (`file.md:line:col`) map straight back to the document with
//! zero offset bookkeeping. All `bpa` blocks share one scope (they concatenate
//! into a single logical file), so a later block can cite an earlier one.

const std = @import("std");
const Allocator = std.mem.Allocator;

/// Mask `source` (a Markdown document) to bpa code: keep the lines inside
/// ```` ```bpa ```` fences, blank everything else, preserving line count and
/// every byte offset. The returned buffer has the same length as `source`
/// except where content is dropped (replaced by nothing but the newline).
pub fn extract(arena: Allocator, source: []const u8) Allocator.Error![]const u8 {
    var out: std.ArrayList(u8) = .empty;
    try out.ensureTotalCapacity(arena, source.len);

    var in_block = false;
    var i: usize = 0;
    while (i < source.len) {
        // find the end of this line (inclusive of the trailing '\n' if present)
        const line_start = i;
        var line_end = i;
        while (line_end < source.len and source[line_end] != '\n') line_end += 1;
        const has_nl = line_end < source.len;
        const line = source[line_start..line_end];

        if (isFenceOpen(line)) {
            // the ```bpa fence line itself is not code — blank it, enter block
            in_block = true;
        } else if (in_block and isFenceClose(line)) {
            // closing ``` — blank it, leave block
            in_block = false;
        } else if (in_block) {
            // inside a bpa block: keep the line verbatim
            try out.appendSlice(arena, line);
        }
        // (else: prose / blank / non-bpa fence — emit nothing but the newline)

        if (has_nl) try out.append(arena, '\n');
        i = line_end + @intFromBool(has_nl);
    }
    return out.items;
}

/// A ```` ```bpa ```` opening fence: ``` (or more backticks) immediately
/// followed by the info string `bpa` (and nothing else but trailing spaces).
fn isFenceOpen(line: []const u8) bool {
    const rest = fenceRest(line) orelse return false;
    const info = std.mem.trim(u8, rest, " \t");
    return std.mem.eql(u8, info, "bpa");
}

/// A closing fence: a run of backticks with no info string.
fn isFenceClose(line: []const u8) bool {
    const rest = fenceRest(line) orelse return false;
    return std.mem.trim(u8, rest, " \t").len == 0;
}

/// If `line` (after optional leading spaces) starts with a run of >= 3
/// backticks, return the text after that run; else null.
fn fenceRest(line: []const u8) ?[]const u8 {
    var s: usize = 0;
    while (s < line.len and (line[s] == ' ' or line[s] == '\t')) s += 1;
    var ticks: usize = 0;
    while (s + ticks < line.len and line[s + ticks] == '`') ticks += 1;
    if (ticks < 3) return null;
    return line[s + ticks ..];
}

// -- tests -----------------------------------------------------------------

const testing = std.testing;

test "extract keeps bpa block content, blanks prose, preserves offsets" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();

    const md =
        \\# Title
        \\
        \\Some prose.
        \\
        \\```bpa
        \\sort Nat
        \\const Z: Nat
        \\```
        \\
        \\more prose
        \\
    ;
    const got = try extract(a, md);
    // the mask preserves NEWLINE count (so line numbers map), though prose
    // bytes are dropped (columns only matter inside bpa blocks, kept verbatim).
    try testing.expectEqual(
        std.mem.count(u8, md, "\n"),
        std.mem.count(u8, got, "\n"),
    );
    // the bpa lines survive, on their original line numbers
    const expect =
        \\
        \\
        \\
        \\
        \\
        \\sort Nat
        \\const Z: Nat
        \\
        \\
        \\
        \\
    ;
    try testing.expectEqualStrings(expect, got);
}

test "ignores non-bpa fences" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    const md =
        \\```
        \\not checked
        \\```
        \\```zig
        \\also not
        \\```
        \\```bpa
        \\sort Nat
        \\```
        \\
    ;
    const got = try extract(a, md);
    try testing.expectEqualStrings(
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\sort Nat
        \\
        \\
    , got);
}
