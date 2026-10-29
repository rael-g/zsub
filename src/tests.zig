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

const DeviceSub = zsub.For(Device);

fn refuseLarge(args: DeviceSub.Args(.create_buffer)) c_int {
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

fn grant(args: zsub.For(std.mem.Allocator.VTable).Args(.alloc)) ?[*]u8 {
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

fn large(args: DeviceSub.Args(.create_buffer)) bool {
    return args[1] > 64;
}

test "a configuration narrowed by a predicate answers only the calls it accepts, and the latest wins" {
    var dev: DeviceSub = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).returns(0);
    _ = dev.when(.create_buffer).with(large).returns(-1);
    _ = dev.when(.create_buffer).with(zsub.argIs(1, @as(u64, 7))).returns(-2);

    try testing.expectEqual(@as(c_int, -2), dev.api().create_buffer.?(dev.api(), 7, null));
    _ = try makeBuffer(dev.api(), 64);
    try testing.expectError(error.Refused, makeBuffer(dev.api(), 65));
    _ = dev.when(.create_buffer).returns(0);
    _ = try makeBuffer(dev.api(), 65);
}

test "calls that match no configuration are reported" {
    var dev: DeviceSub = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).with(large).returns(-1);

    try testing.expectError(error.Refused, makeBuffer(dev.api(), 65));
    try dev.noUnconfiguredCalls();
    _ = try makeBuffer(dev.api(), 1);
    try testing.expectError(error.UnexpectedCalls, dev.noUnconfiguredCalls());
}

const Store = struct {
    load: *const fn (key: u32) error{Missing}!u32,
};

test "a slot returning an error union can be made to fail" {
    var store: zsub.For(Store) = undefined;
    try store.init();
    defer store.deinit();

    try testing.expectEqual(@as(u32, 0), try store.api().load(1));
    _ = store.when(.load).fails(error.Missing);
    try testing.expectError(error.Missing, store.api().load(1));
}

const Wide = extern struct {
    call: ?*const fn (?*Wide, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) callconv(.c) u32 = null,
};

test "a slot with many parameters is substituted" {
    var wide: zsub.For(Wide) = undefined;
    try wide.init();
    defer wide.deinit();
    _ = wide.when(.call).returns(9);

    try testing.expectEqual(@as(u32, 9), wide.api().call.?(wide.api(), 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12));
    try testing.expectEqual(@as(u8, 12), wide.received(.call).lastArgs().?[12]);
}

test "calls across substitutes are verified in order" {
    var a: DeviceSub = undefined;
    try a.init();
    defer a.deinit();
    var b: DeviceSub = undefined;
    try b.init();
    defer b.deinit();

    _ = try makeBuffer(a.api(), 1);
    b.api().destroy_buffer.?(b.api(), 1);
    try zsub.inOrder(.{ a.received(.create_buffer), b.received(.destroy_buffer) });
    try testing.expectError(error.UnexpectedCalls, zsub.inOrder(.{ b.received(.destroy_buffer), a.received(.create_buffer) }));
    try testing.expectError(error.UnexpectedCalls, zsub.inOrder(.{ a.received(.create_buffer), a.received(.name) }));
}

const Registry = extern struct {
    id: ?*const fn (?*Registry, name: [*c]const u8) callconv(.c) u32 = null,
    make: ?*const fn (?*Registry, out: ?*u32) callconv(.c) c_int = null,
};

test "fresh values answered and written by one substitute never repeat" {
    var reg: zsub.For(Registry) = undefined;
    try reg.init();
    defer reg.deinit();
    _ = reg.when(.id).returnsFresh();
    _ = reg.when(.make).writesFresh(1);

    var made: u32 = 0;
    const a = reg.api().id.?(reg.api(), "a");
    _ = reg.api().make.?(reg.api(), &made);
    const b = reg.api().id.?(reg.api(), "a");
    try testing.expect(a != 0 and made != 0 and b != 0);
    try testing.expect(a != made and made != b and a != b);
}

fn valid(args: DeviceSub.Args(.destroy_buffer)) bool {
    return args[1] != 0;
}

test "calls are verified by their arguments, and a filter that cannot see every call fails" {
    var dev: DeviceSub = undefined;
    try dev.init();
    defer dev.deinit();
    _ = dev.when(.create_buffer).writesFresh(2);

    dev.api().destroy_buffer.?(dev.api(), 0);
    const buffer = try makeBuffer(dev.api(), 1);
    dev.api().destroy_buffer.?(dev.api(), buffer);
    try dev.received(.destroy_buffer).times(2);
    try dev.received(.destroy_buffer).where(valid).sameAs(dev.received(.create_buffer));
    try testing.expectEqual(buffer, dev.received(.destroy_buffer).where(valid).lastArgs().?[1]);
    try dev.received(.destroy_buffer).where(zsub.argIsNot(1, @as(u64, 0))).times(1);
    try dev.received(.destroy_buffer).where(zsub.argIs(1, @as(u64, 0))).times(1);

    for (0..zsub.history_len) |_| dev.api().destroy_buffer.?(dev.api(), 0);
    try dev.received(.destroy_buffer).times(zsub.history_len + 2);
    try testing.expectError(error.UnexpectedCalls, dev.received(.destroy_buffer).where(valid).times(1));
}

const Large = blk: {
    const count = 200;
    @setEvalBranchQuota(100_000);
    var names: [count][]const u8 = undefined;
    for (&names, 0..) |*n, i| n.* = std.fmt.comptimePrint("slot{d}", .{i});
    const Slot = ?*const fn (?*anyopaque, u32) callconv(.c) u32;
    break :blk @Struct(.@"extern", null, &names, &@splat(Slot), &@splat(.{}));
};

test "a table with many slots is substituted" {
    var many: zsub.For(Large) = undefined;
    try many.init();
    defer many.deinit();
    _ = many.when(.slot199).returnsFresh();

    try testing.expect(many.api().slot199.?(many.context(), 1) != 0);
    try many.received(.slot199).times(1);
    try many.received(.slot0).never();
}
