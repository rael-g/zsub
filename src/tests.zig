//! The behaviour of zsub's substitutes, one table shape at a time.

const std = @import("std");
const zsub = @import("zsub.zig");
const testing = std.testing;

const Device = extern struct {
    handle: ?*anyopaque = null,
    create_buffer: ?*const fn (?*Device, size: u64, out: ?*u64) callconv(.c) c_int = null,
    destroy_buffer: ?*const fn (?*Device, buffer: u64) callconv(.c) void = null,
    name: ?*const fn (?*Device) callconv(.c) [*c]const u8 = null,
};

const Callbacks = extern struct {
    on_value: ?*const fn (value: c_int) callconv(.c) c_int = null,
    on_pair: ?*const fn (a: c_int, b: c_int) callconv(.c) void = null,
};

fn makeBuffer(dev: *Device, size: u64) !u64 {
    var buffer: u64 = 0;
    if (dev.create_buffer.?(dev, size, &buffer) != 0) return error.Refused;
    return buffer;
}

test "an unconfigured slot answers zero and counts the call" {
    var dev: zsub.For(Device) = undefined;
    try dev.init();
    defer dev.deinit();

    try testing.expectEqual(@as(u64, 0), try makeBuffer(dev.api(), 16));
    try testing.expectEqual(@as([*c]const u8, null), dev.api().name.?(dev.api()));
    try dev.received(.create_buffer).times(1);
    try dev.received(.destroy_buffer).never();
}

test "a configured value is returned on every call" {
    var dev: zsub.For(Device) = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).returns(-1);

    try testing.expectError(error.Refused, makeBuffer(dev.api(), 16));
    try testing.expectError(error.Refused, makeBuffer(dev.api(), 16));
    try dev.received(.create_buffer).times(2);
}

test "a sequence is returned in order and its last value repeats" {
    var dev: zsub.For(Device) = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).returnsSeq(&.{ 0, 0, -1 });

    _ = try makeBuffer(dev.api(), 1);
    _ = try makeBuffer(dev.api(), 1);
    try testing.expectError(error.Refused, makeBuffer(dev.api(), 1));
    try testing.expectError(error.Refused, makeBuffer(dev.api(), 1));
}

fn refuseLarge(args: std.meta.Tuple(&.{ ?*Device, u64, ?*u64 })) c_int {
    return if (args[1] > 64) -1 else 0;
}

test "a slot can compute its answer from the call's arguments" {
    var dev: zsub.For(Device) = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).does(refuseLarge);

    _ = try makeBuffer(dev.api(), 64);
    try testing.expectError(error.Refused, makeBuffer(dev.api(), 65));
}

test "a fresh value is written through an out argument on each call" {
    var dev: zsub.For(Device) = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).writesFresh(2);

    const a = try makeBuffer(dev.api(), 1);
    const b = try makeBuffer(dev.api(), 1);
    try testing.expect(a != 0);
    try testing.expect(a != b);
}

test "the latest arguments are kept and creates can be balanced against destroys" {
    var dev: zsub.For(Device) = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).writesFresh(2);

    const buffer = try makeBuffer(dev.api(), 32);
    try testing.expectEqual(@as(u64, 32), dev.received(.create_buffer).lastArgs().?[1]);
    try testing.expectError(error.UnexpectedCalls, dev.received(.create_buffer).sameAs(dev.received(.destroy_buffer)));
    dev.api().destroy_buffer.?(dev.api(), buffer);
    try dev.received(.create_buffer).sameAs(dev.received(.destroy_buffer));
    try testing.expectEqual(buffer, dev.received(.destroy_buffer).lastArgs().?[1]);
}

test "two substitutes of a table with a way back share their slot functions and not their state" {
    var a: zsub.For(Device) = undefined;
    try a.init();
    defer a.deinit();
    var b: zsub.For(Device) = undefined;
    try b.init();
    defer b.deinit();
    _ = b.when(.create_buffer).returns(-1);

    try testing.expectEqual(a.api().create_buffer, b.api().create_buffer);
    _ = try makeBuffer(a.api(), 1);
    try testing.expectError(error.Refused, makeBuffer(b.api(), 1));
    try a.received(.create_buffer).times(1);
    try b.received(.create_buffer).times(1);
}

test "substitutes of a table with no way back hold independent state" {
    var subs: [10]zsub.For(Callbacks) = undefined;
    for (&subs, 0..) |*s, i| {
        try s.init();
        _ = s.when(.on_value).returns(@intCast(i));
    }
    defer for (&subs) |*s| s.deinit();

    for (&subs, 0..) |*s, i| try testing.expectEqual(@as(c_int, @intCast(i)), s.api().on_value.?(7));
    for (&subs) |*s| try s.received(.on_value).times(1);
    try testing.expectEqual(@as(c_int, 7), subs[3].received(.on_value).lastArgs().?[0]);
}

test "a table with no way back refuses a substitute past its capacity and takes one again after a deinit" {
    var subs: [2]zsub.ForN(Callbacks, 2) = undefined;
    for (&subs) |*s| try s.init();
    var extra: zsub.ForN(Callbacks, 2) = undefined;
    try testing.expectError(error.OutOfSubstitutes, extra.init());
    subs[0].deinit();
    try extra.init();
    extra.deinit();
    subs[1].deinit();
}

fn grant(args: std.meta.ArgsTuple(@typeInfo(@FieldType(std.mem.Allocator.VTable, "alloc")).pointer.child)) ?[*]u8 {
    _ = args;
    return &granted;
}

var granted: [64]u8 = undefined;

test "a standard library interface is substituted through its context" {
    var vtable: zsub.For(std.mem.Allocator.VTable) = undefined;
    try vtable.init();
    defer vtable.deinit();
    const allocator: std.mem.Allocator = .{ .ptr = vtable.context(), .vtable = vtable.api() };

    try testing.expectError(error.OutOfMemory, allocator.alloc(u8, 8));
    _ = vtable.when(.alloc).does(grant);
    const bytes = try allocator.alloc(u8, 8);
    try testing.expectEqual(@as([*]u8, &granted), bytes.ptr);
    try vtable.received(.alloc).times(2);
    try testing.expectEqual(@as(usize, 8), vtable.received(.alloc).lastArgs().?[1]);
}
