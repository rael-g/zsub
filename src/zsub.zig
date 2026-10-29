//! Substitutes for tables of function pointers: a C vtable, a `ptr` + `vtable` pair of the
//! standard library, or any struct whose fields are function pointers. A substitute answers every
//! slot with zero until a test configures it, and records each call so the test can verify it.

const std = @import("std");

/// How many substitutes of one table can be live at once when some of its slots have no way back
/// to their substitute.
pub const default_capacity = 16;

/// What `received` reports when a verification fails.
pub const VerificationError = error{UnexpectedCalls};

/// A substitute of `T` with the default capacity.
pub fn For(comptime T: type) type {
    return ForN(T, default_capacity);
}

/// A substitute of `T`, a struct whose function pointer fields are its slots. A slot finds its
/// substitute through its first argument when that argument points to the table or is the
/// substitute's `context`; any other slot is served from a pool of `capacity` copies, so at most
/// `capacity` substitutes of `T` can be live at once.
pub fn ForN(comptime T: type, comptime capacity: usize) type {
    const fields = @typeInfo(T).@"struct".fields;
    comptime var needs_pool = false;
    inline for (fields) |f| {
        if (fnOf(f.type)) |F| {
            if (wayBack(T, F) == .pool) needs_pool = true;
        }
    }
    const pooled = needs_pool;
    const pool_size = if (pooled) capacity else 0;

    return struct {
        const Self = @This();

        /// The slots of `T`, by name.
        pub const Slot = std.meta.FieldEnum(T);

        table: T,
        slots: States(T),
        fresh: u64,
        index: usize,

        var owners: [pool_size]std.atomic.Value(?*Self) = @splat(.init(null));

        /// Makes `self` a substitute whose slots all answer zero. `self` must not move while it
        /// is live. Fails when the table needs the pool and every one of its `capacity` places is
        /// taken.
        pub fn init(self: *Self) error{OutOfSubstitutes}!void {
            self.* = .{ .table = undefined, .slots = undefined, .fresh = 0, .index = 0 };
            if (pooled) self.index = try claim(self);
            inline for (fields) |f| {
                if (comptime fnOf(f.type)) |F| {
                    @field(self.slots, f.name) = .{};
                    @field(self.table, f.name) = slotPointer(F, f.name, self.index);
                } else if (f.defaultValue()) |d| {
                    @field(self.table, f.name) = d;
                } else {
                    @field(self.table, f.name) = std.mem.zeroes(f.type);
                }
            }
        }

        /// Gives back the place `self` took in the pool. A slot called after this panics.
        pub fn deinit(self: *Self) void {
            if (pooled) owners[self.index].store(null, .release);
        }

        /// The table to hand to the code under test.
        pub fn api(self: *Self) *T {
            return &self.table;
        }

        /// The pointer to hand to the code under test where a slot's first argument is an
        /// opaque context, as the `ptr` of a standard library interface.
        pub fn context(self: *Self) *anyopaque {
            return self;
        }

        /// Configures what `slot` does when called.
        pub fn when(self: *Self, comptime slot: Slot) When(SlotFn(slot)) {
            return .{ .state = &@field(self.slots, @tagName(slot)) };
        }

        /// What `slot` has received so far.
        pub fn received(self: *Self, comptime slot: Slot) Received(SlotFn(slot)) {
            const state = &@field(self.slots, @tagName(slot));
            return .{ .name = @tagName(slot), .calls = @atomicLoad(u32, &state.calls, .acquire), .last = state.last };
        }

        fn SlotFn(comptime slot: Slot) type {
            const name = @tagName(slot);
            inline for (fields) |f| {
                if (comptime std.mem.eql(u8, f.name, name)) {
                    return fnOf(f.type) orelse @compileError("zsub: '" ++ name ++ "' of " ++ @typeName(T) ++ " is not a function pointer");
                }
            }
            unreachable;
        }

        fn claim(self: *Self) error{OutOfSubstitutes}!usize {
            for (&owners, 0..) |*owner, i| {
                if (owner.cmpxchgStrong(null, self, .acq_rel, .acquire) == null) return i;
            }
            std.debug.print("zsub: all {d} substitutes of {s} are live; raise the capacity with zsub.ForN\n", .{ capacity, @typeName(T) });
            return error.OutOfSubstitutes;
        }

        fn slotPointer(comptime F: type, comptime name: []const u8, index: usize) *const F {
            if (comptime wayBack(T, F) == .pool) {
                const copies = comptime blk: {
                    var all: [pool_size]*const F = undefined;
                    for (&all, 0..) |*p, i| p.* = trampoline(F, name, .{ .pool = i });
                    break :blk all;
                };
                return copies[index];
            }
            return comptime trampoline(F, name, .self);
        }

        fn trampoline(comptime F: type, comptime name: []const u8, comptime locate: Locate) *const F {
            const Impl = struct {
                fn call(args: std.meta.ArgsTuple(F)) Return(F) {
                    return owner(args).dispatch(name, F, args);
                }

                fn owner(args: std.meta.ArgsTuple(F)) *Self {
                    switch (locate) {
                        .pool => |i| return owners[i].load(.acquire) orelse @panic("zsub: slot '" ++ name ++ "' of " ++ @typeName(T) ++ " called after deinit"),
                        .self => switch (comptime wayBack(T, F)) {
                            .table => {
                                const table = toPtr(T, args[0]) orelse @panic("zsub: slot '" ++ name ++ "' of " ++ @typeName(T) ++ " called with a null table");
                                return @fieldParentPtr("table", table);
                            },
                            .context => return toPtr(Self, args[0]) orelse @panic("zsub: slot '" ++ name ++ "' of " ++ @typeName(T) ++ " called with a null context"),
                            .pool => unreachable,
                        },
                    }
                }
            };
            return forward(F, Impl.call);
        }

        fn dispatch(self: *Self, comptime name: []const u8, comptime F: type, args: std.meta.ArgsTuple(F)) Return(F) {
            const state = &@field(self.slots, name);
            _ = @atomicRmw(u32, &state.calls, .Add, 1, .acq_rel);
            state.last = args;
            if (state.fresh_out) |k| {
                inline for (args, 0..) |arg, i| {
                    if (comptime isIntOut(@TypeOf(arg))) {
                        if (i == k) writeFresh(self, arg);
                    }
                }
            }
            return switch (state.behavior) {
                .zero => zeroOf(Return(F)),
                .value => |v| v,
                .does => |f| f(args),
                .sequence => |*seq| blk: {
                    const v = seq.values[seq.next];
                    if (seq.next + 1 < seq.values.len) seq.next += 1;
                    break :blk v;
                },
            };
        }

        fn writeFresh(self: *Self, out: anytype) void {
            const value = @atomicRmw(u64, &self.fresh, .Add, 1, .acq_rel) + 1;
            if (toPtr(Pointee(@TypeOf(out)), out)) |p| p.* = @intCast(value);
        }
    };
}

/// The configuration of one slot of a substitute, returned by `when`.
pub fn When(comptime F: type) type {
    return struct {
        const Self = @This();
        state: *SlotState(F),

        /// Answers every call with `value`.
        pub fn returns(self: Self, value: Return(F)) Self {
            self.state.behavior = .{ .value = value };
            return self;
        }

        /// Answers each call with the next of `values`, repeating the last one once they run out.
        /// `values` must outlive the substitute and hold at least one value.
        pub fn returnsSeq(self: Self, values: []const Return(F)) Self {
            self.state.behavior = .{ .sequence = .{ .values = values, .next = 0 } };
            return self;
        }

        /// Answers each call with what `f` returns for the call's arguments.
        pub fn does(self: Self, f: *const fn (std.meta.ArgsTuple(F)) Return(F)) Self {
            self.state.behavior = .{ .does = f };
            return self;
        }

        /// Writes a value no earlier call of this substitute wrote through argument `k`, which
        /// must be a pointer to an integer.
        pub fn writesFresh(self: Self, comptime k: usize) Self {
            const params = @typeInfo(F).@"fn".params;
            if (comptime (k >= params.len or !isIntOut(params[k].type.?))) @compileError("zsub: argument " ++ std.fmt.comptimePrint("{d}", .{k}) ++ " is not a pointer to an integer");
            self.state.fresh_out = k;
            return self;
        }
    };
}

/// What a slot of a substitute has received.
pub fn Received(comptime F: type) type {
    return struct {
        const Self = @This();
        name: []const u8,
        calls: u32,
        last: ?std.meta.ArgsTuple(F),

        /// Fails unless the slot was called exactly `n` times.
        pub fn times(self: Self, n: u32) VerificationError!void {
            if (self.calls != n) return fail(self.name, "{d} calls expected, {d} received", .{ n, self.calls });
        }

        /// Fails if the slot was called.
        pub fn never(self: Self) VerificationError!void {
            return self.times(0);
        }

        /// Fails unless the slot was called at least `n` times.
        pub fn atLeast(self: Self, n: u32) VerificationError!void {
            if (self.calls < n) return fail(self.name, "at least {d} calls expected, {d} received", .{ n, self.calls });
        }

        /// Fails unless the slot was called as many times as `other`.
        pub fn sameAs(self: Self, other: anytype) VerificationError!void {
            if (self.calls != other.calls) return fail(self.name, "as many calls as '{s}' expected: {d} against {d}", .{ other.name, self.calls, other.calls });
        }

        /// The arguments of the latest call, or null when the slot was never called.
        pub fn lastArgs(self: Self) ?std.meta.ArgsTuple(F) {
            return self.last;
        }
    };
}

fn fail(name: []const u8, comptime fmt: []const u8, args: anytype) VerificationError {
    std.debug.print("zsub: slot '{s}': " ++ fmt ++ "\n", .{name} ++ args);
    return error.UnexpectedCalls;
}

fn SlotState(comptime F: type) type {
    const R = Return(F);
    const Args = std.meta.ArgsTuple(F);
    return struct {
        calls: u32 = 0,
        last: ?Args = null,
        fresh_out: ?usize = null,
        behavior: union(enum) {
            zero,
            value: R,
            does: *const fn (Args) R,
            sequence: struct { values: []const R, next: usize },
        } = .zero,
    };
}

fn States(comptime T: type) type {
    const fields = @typeInfo(T).@"struct".fields;
    comptime var count = 0;
    inline for (fields) |f| {
        if (fnOf(f.type) != null) count += 1;
    }
    var names: [count][]const u8 = undefined;
    var types: [count]type = undefined;
    var i = 0;
    for (fields) |f| {
        if (fnOf(f.type)) |F| {
            names[i] = f.name;
            types[i] = SlotState(F);
            i += 1;
        }
    }
    return @Struct(.auto, null, &names, &types, &@splat(.{}));
}

const Locate = union(enum) { self, pool: usize };

const WayBack = enum { table, context, pool };

fn wayBack(comptime T: type, comptime F: type) WayBack {
    const params = @typeInfo(F).@"fn".params;
    if (params.len == 0) return .pool;
    const P = params[0].type orelse return .pool;
    const Ptr = switch (@typeInfo(P)) {
        .optional => |o| o.child,
        else => P,
    };
    const ptr = switch (@typeInfo(Ptr)) {
        .pointer => |p| p,
        else => return .pool,
    };
    if (ptr.size != .one and ptr.size != .c) return .pool;
    if (ptr.child == T) return .table;
    if (ptr.child == anyopaque and ptr.size == .one) return .context;
    return .pool;
}

fn fnOf(comptime P: type) ?type {
    const Ptr = switch (@typeInfo(P)) {
        .optional => |o| o.child,
        else => P,
    };
    return switch (@typeInfo(Ptr)) {
        .pointer => |p| if (@typeInfo(p.child) == .@"fn") p.child else null,
        else => null,
    };
}

fn Return(comptime F: type) type {
    return @typeInfo(F).@"fn".return_type.?;
}

fn isIntOut(comptime P: type) bool {
    const Ptr = switch (@typeInfo(P)) {
        .optional => |o| o.child,
        else => P,
    };
    return switch (@typeInfo(Ptr)) {
        .pointer => |p| !p.is_const and (p.size == .one or p.size == .c) and @typeInfo(p.child) == .int,
        else => false,
    };
}

fn Pointee(comptime P: type) type {
    const Ptr = switch (@typeInfo(P)) {
        .optional => |o| o.child,
        else => P,
    };
    return @typeInfo(Ptr).pointer.child;
}

fn toPtr(comptime Child: type, p: anytype) ?*Child {
    const address = @intFromPtr(p);
    return if (address == 0) null else @ptrFromInt(address);
}

fn zeroOf(comptime R: type) R {
    return switch (@typeInfo(R)) {
        .void => {},
        .error_union => |e| zeroOf(e.payload),
        else => std.mem.zeroes(R),
    };
}

fn forward(comptime F: type, comptime call: anytype) *const F {
    const info = @typeInfo(F).@"fn";
    const R = info.return_type.?;
    const cc = info.calling_convention;
    const P = info.params;
    inline for (P) |p| {
        if (p.type == null) @compileError("zsub: a slot with an anytype parameter cannot be substituted");
    }
    if (info.is_var_args) @compileError("zsub: a variadic slot cannot be substituted");
    return switch (P.len) {
        0 => &struct {
            fn f() callconv(cc) R {
                return call(.{});
            }
        }.f,
        1 => &struct {
            fn f(a0: P[0].type.?) callconv(cc) R {
                return call(.{a0});
            }
        }.f,
        2 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?) callconv(cc) R {
                return call(.{ a0, a1 });
            }
        }.f,
        3 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2 });
            }
        }.f,
        4 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3 });
            }
        }.f,
        5 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4 });
            }
        }.f,
        6 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5 });
            }
        }.f,
        7 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6 });
            }
        }.f,
        8 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7 });
            }
        }.f,
        else => @compileError("zsub: slots with more than 8 parameters are not supported yet"),
    };
}

test {
    _ = @import("tests.zig");
}
