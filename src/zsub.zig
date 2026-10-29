//! Substitutes for tables of function pointers: a C vtable, a `ptr` + `vtable` pair of the
//! standard library, or any struct whose fields are function pointers. A substitute answers every
//! slot with zero until a test configures it, and records each call so the test can verify it.

const std = @import("std");

/// How many substitutes of one table can be live at once when some of its slots have no way back
/// to their substitute.
pub const default_capacity = 16;

/// How many configurations one slot of a substitute can hold.
pub const max_rules = 16;

/// How many calls of one slot `where` can look back on.
pub const history_len = 32;

/// What `received` reports when a verification fails.
pub const VerificationError = error{UnexpectedCalls};

var sequence: std.atomic.Value(u64) = .init(0);

/// Fails unless every slot in `slots`, a tuple of `received` reports, was called, and each one's
/// calls all came before the first call of the one after it.
pub fn inOrder(slots: anytype) VerificationError!void {
    inline for (slots) |r| {
        if (r.calls == 0) return fail(r.name, "a call was expected in order, none received", .{});
    }
    inline for (1..slots.len) |i| {
        if (slots[i - 1].last_seq > slots[i].first_seq) return fail(slots[i].name, "was called before the latest call of '{s}'", .{slots[i - 1].name});
    }
}

/// A matcher accepting the calls whose argument `k` equals `value`, for `with` and `where`.
pub fn argIs(comptime k: usize, comptime value: anytype) type {
    return struct {
        pub fn matches(args: anytype) bool {
            return std.meta.eql(args[k], value);
        }
    };
}

/// A matcher accepting the calls whose argument `k` differs from `value`, for `with` and `where`.
pub fn argIsNot(comptime k: usize, comptime value: anytype) type {
    return struct {
        pub fn matches(args: anytype) bool {
            return !std.meta.eql(args[k], value);
        }
    };
}

fn predicate(comptime Args: type, comptime matcher: anytype) *const fn (Args) bool {
    if (@TypeOf(matcher) == type) {
        return &struct {
            fn f(args: Args) bool {
                return matcher.matches(args);
            }
        }.f;
    }
    return matcher;
}

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
    @setEvalBranchQuota(1000 + 100 * fields.len);
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

        /// The tuple of the arguments `slot` is called with.
        pub fn Args(comptime slot: Slot) type {
            return std.meta.ArgsTuple(SlotFn(slot));
        }

        /// Configures what `slot` does when called. A later configuration takes precedence over
        /// an earlier one for the calls both match.
        pub fn when(self: *Self, comptime slot: Slot) When(SlotFn(slot)) {
            return .{ .state = &@field(self.slots, @tagName(slot)), .predicate = null };
        }

        /// Fails if a slot was called with no configuration matching the call.
        pub fn noUnconfiguredCalls(self: *Self) VerificationError!void {
            inline for (fields) |f| {
                if (comptime fnOf(f.type) != null) {
                    const state = &@field(self.slots, f.name);
                    const n = @atomicLoad(u32, &state.unconfigured, .acquire);
                    if (n > 0) return fail(f.name, "{d} calls matched no configuration", .{n});
                }
            }
        }

        /// What `slot` has received so far.
        pub fn received(self: *Self, comptime slot: Slot) Received(SlotFn(slot)) {
            const state = &@field(self.slots, @tagName(slot));
            const calls = @atomicLoad(u32, &state.calls, .acquire);
            return .{ .name = @tagName(slot), .calls = calls, .last = state.last, .first_seq = state.first_seq, .last_seq = state.last_seq, .history = state.history[0..@min(calls, history_len)], .overflowed = false };
        }

        fn SlotFn(comptime slot: Slot) type {
            const name = @tagName(slot);
            return fnOf(@FieldType(T, name)) orelse @compileError("zsub: '" ++ name ++ "' of " ++ @typeName(T) ++ " is not a function pointer");
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
            const at = sequence.fetchAdd(1, .acq_rel) + 1;
            const before = @atomicRmw(u32, &state.calls, .Add, 1, .acq_rel);
            if (before == 0) state.first_seq = at;
            state.history[before % history_len] = args;
            state.last_seq = at;
            state.last = args;
            if (state.fresh_out) |k| {
                inline for (args, 0..) |arg, i| {
                    if (comptime isIntOut(@TypeOf(arg))) {
                        if (i == k) writeFresh(self, arg);
                    }
                }
            }
            inline for (args, 0..) |arg, k| {
                if (comptime @TypeOf(state.outs[k]) != void) {
                    if (state.outs[k]) |value| {
                        if (toPtr(Pointee(@TypeOf(arg)), arg)) |p| p.* = value;
                    }
                }
            }
            var i = state.rule_count;
            while (i > 0) {
                i -= 1;
                const rule = &state.rules[i];
                if (rule.predicate) |matches| {
                    if (!matches(args)) continue;
                }
                return switch (rule.behavior) {
                    .value => |v| v,
                    .fresh => freshOf(Return(F), self.nextFresh()),
                    .does => |f| f(args),
                    .does_with => |d| d.call(d.ctx, args),
                    .sequence => |*seq| blk: {
                        const v = seq.values[seq.next];
                        if (seq.next + 1 < seq.values.len) seq.next += 1;
                        break :blk v;
                    },
                };
            }
            if (state.fresh_out == null and !state.writes_out) _ = @atomicRmw(u32, &state.unconfigured, .Add, 1, .acq_rel);
            return zeroOf(Return(F));
        }

        fn writeFresh(self: *Self, out: anytype) void {
            const value = self.nextFresh();
            if (toPtr(Pointee(@TypeOf(out)), out)) |p| p.* = @intCast(value);
        }

        fn nextFresh(self: *Self) u64 {
            return @atomicRmw(u64, &self.fresh, .Add, 1, .acq_rel) + 1;
        }
    };
}

/// The configuration of one slot of a substitute, returned by `when`.
pub fn When(comptime F: type) type {
    const R = Return(F);
    const Args = std.meta.ArgsTuple(F);
    return struct {
        const Self = @This();
        state: *SlotState(F),
        predicate: ?*const fn (Args) bool,

        /// Narrows what follows to the calls whose arguments `matcher` accepts: a function of the
        /// arguments, or a matcher such as `argIs`.
        pub fn with(self: Self, comptime matcher: anytype) Self {
            return .{ .state = self.state, .predicate = predicate(Args, matcher) };
        }

        /// Answers the calls with `value`.
        pub fn returns(self: Self, value: R) Self {
            return self.add(.{ .value = value });
        }

        /// Answers the calls with the error `err`. Only for a slot that returns an error union.
        pub fn fails(self: Self, err: ErrorOf(R)) Self {
            return self.add(.{ .value = err });
        }

        /// Answers each call with the next of `values`, repeating the last one once they run out.
        /// `values` must outlive the substitute and hold at least one value.
        pub fn returnsSeq(self: Self, values: []const R) Self {
            return self.add(.{ .sequence = .{ .values = values, .next = 0 } });
        }

        /// Answers each call with a value no earlier call of this substitute answered or wrote.
        /// Only for a slot that returns an integer.
        pub fn returnsFresh(self: Self) Self {
            if (comptime @typeInfo(R) != .int) @compileError("zsub: returnsFresh is only for a slot that returns an integer, not " ++ @typeName(R));
            return self.add(.fresh);
        }

        /// Answers each call with what `f` returns for the call's arguments.
        pub fn does(self: Self, f: *const fn (Args) R) Self {
            return self.add(.{ .does = f });
        }

        /// Answers each call with what `f` returns for `ctx` and the call's arguments, so the
        /// answer can read and change state the test owns. `ctx` must outlive the substitute.
        pub fn doesWith(self: Self, ctx: anytype, comptime f: fn (@TypeOf(ctx), Args) R) Self {
            const Ctx = @TypeOf(ctx);
            const call = struct {
                fn call(erased: *anyopaque, args: Args) R {
                    return f(@as(Ctx, @ptrCast(@alignCast(erased))), args);
                }
            }.call;
            return self.add(.{ .does_with = .{ .ctx = @ptrCast(@constCast(ctx)), .call = call } });
        }

        /// Writes `value` through argument `k`, a pointer the slot writes its result through, on
        /// every call of the slot.
        pub fn writes(self: Self, comptime k: usize, value: OutOf(F, k)) Self {
            self.state.outs[k] = value;
            self.state.writes_out = true;
            return self;
        }

        /// Writes a value no earlier call of this substitute wrote through argument `k`, which
        /// must be a pointer to an integer, on every call of the slot.
        pub fn writesFresh(self: Self, comptime k: usize) Self {
            const params = @typeInfo(F).@"fn".params;
            if (comptime (k >= params.len or !isIntOut(params[k].type.?))) @compileError("zsub: argument " ++ std.fmt.comptimePrint("{d}", .{k}) ++ " is not a pointer to an integer");
            self.state.fresh_out = k;
            return self;
        }

        fn add(self: Self, behavior: SlotState(F).Behavior) Self {
            if (self.state.rule_count == max_rules) @panic("zsub: a slot holds at most " ++ std.fmt.comptimePrint("{d}", .{max_rules}) ++ " configurations");
            self.state.rules[self.state.rule_count] = .{ .predicate = self.predicate, .behavior = behavior };
            self.state.rule_count += 1;
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
        first_seq: u64,
        last_seq: u64,
        history: []const std.meta.ArgsTuple(F),
        overflowed: bool,

        /// The calls whose arguments `matcher` accepts: a function of the arguments, or a matcher
        /// such as `argIs`. It sees the latest `history_len` calls, and every verification of it
        /// fails once the slot was called more often than that.
        pub fn where(self: Self, comptime matcher: anytype) Self {
            const matches = predicate(std.meta.ArgsTuple(F), matcher);
            var picked = self;
            picked.overflowed = self.calls > history_len;
            picked.calls = 0;
            picked.last = null;
            for (self.history) |args| {
                if (matches(args)) {
                    picked.calls += 1;
                    picked.last = args;
                }
            }
            return picked;
        }

        /// Fails unless the slot was called exactly `n` times.
        pub fn times(self: Self, n: u32) VerificationError!void {
            try self.complete();
            if (self.calls != n) return fail(self.name, "{d} calls expected, {d} received", .{ n, self.calls });
        }

        /// Fails if the slot was called.
        pub fn never(self: Self) VerificationError!void {
            return self.times(0);
        }

        /// Fails unless the slot was called at least `n` times.
        pub fn atLeast(self: Self, n: u32) VerificationError!void {
            try self.complete();
            if (self.calls < n) return fail(self.name, "at least {d} calls expected, {d} received", .{ n, self.calls });
        }

        /// Fails unless the slot was called as many times as `other`.
        pub fn sameAs(self: Self, other: anytype) VerificationError!void {
            try self.complete();
            try other.complete();
            if (self.calls != other.calls) return fail(self.name, "as many calls as '{s}' expected: {d} against {d}", .{ other.name, self.calls, other.calls });
        }

        fn complete(self: Self) VerificationError!void {
            if (self.overflowed) return fail(self.name, "called more than {d} times, so a filter by arguments cannot see every call", .{history_len});
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
        const Behavior = union(enum) {
            value: R,
            fresh,
            does: *const fn (Args) R,
            does_with: struct { ctx: *anyopaque, call: *const fn (*anyopaque, Args) R },
            sequence: struct { values: []const R, next: usize },
        };
        const Rule = struct { predicate: ?*const fn (Args) bool, behavior: Behavior };

        calls: u32 = 0,
        first_seq: u64 = 0,
        last_seq: u64 = 0,
        unconfigured: u32 = 0,
        last: ?Args = null,
        history: [history_len]Args = undefined,
        fresh_out: ?usize = null,
        outs: Outs(F) = noOuts(Outs(F)),
        writes_out: bool = false,
        rules: [max_rules]Rule = undefined,
        rule_count: usize = 0,
    };
}

fn OutOf(comptime F: type, comptime k: usize) type {
    const params = @typeInfo(F).@"fn".params;
    if (k >= params.len) @compileError("zsub: the slot has no argument " ++ std.fmt.comptimePrint("{d}", .{k}));
    return OutPointee(params[k].type.?) orelse @compileError("zsub: argument " ++ std.fmt.comptimePrint("{d}", .{k}) ++ " is not a pointer the slot can write through");
}

fn OutPointee(comptime P: type) ?type {
    const Ptr = switch (@typeInfo(P)) {
        .optional => |o| o.child,
        else => P,
    };
    return switch (@typeInfo(Ptr)) {
        .pointer => |p| if (!p.is_const and (p.size == .one or p.size == .c) and p.child != anyopaque and @typeInfo(p.child) != .@"fn" and @typeInfo(p.child) != .@"opaque") p.child else null,
        else => null,
    };
}

fn Outs(comptime F: type) type {
    const params = @typeInfo(F).@"fn".params;
    var types: [params.len]type = undefined;
    for (params, &types) |p, *t| t.* = if (OutPointee(p.type.?)) |V| ?V else void;
    return @Tuple(&types);
}

fn noOuts(comptime O: type) O {
    var o: O = undefined;
    inline for (@typeInfo(O).@"struct".fields) |f| @field(o, f.name) = if (f.type == void) {} else null;
    return o;
}

fn States(comptime T: type) type {
    const fields = @typeInfo(T).@"struct".fields;
    @setEvalBranchQuota(1000 + 100 * fields.len);
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

fn ErrorOf(comptime R: type) type {
    return switch (@typeInfo(R)) {
        .error_union => |e| e.error_set,
        else => @compileError("zsub: fails is only for a slot that returns an error union, not " ++ @typeName(R)),
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

fn freshOf(comptime R: type, value: u64) R {
    return switch (@typeInfo(R)) {
        .int => @intCast(value),
        else => unreachable,
    };
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
        9 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8 });
            }
        }.f,
        10 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9 });
            }
        }.f,
        11 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 });
            }
        }.f,
        12 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 });
            }
        }.f,
        13 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 });
            }
        }.f,
        14 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 });
            }
        }.f,
        15 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14 });
            }
        }.f,
        16 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 });
            }
        }.f,
        17 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 });
            }
        }.f,
        18 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17 });
            }
        }.f,
        19 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18 });
            }
        }.f,
        20 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19 });
            }
        }.f,
        21 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20 });
            }
        }.f,
        22 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21 });
            }
        }.f,
        23 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22 });
            }
        }.f,
        24 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23 });
            }
        }.f,
        25 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24 });
            }
        }.f,
        26 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?, a25: P[25].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25 });
            }
        }.f,
        27 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?, a25: P[25].type.?, a26: P[26].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26 });
            }
        }.f,
        28 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?, a25: P[25].type.?, a26: P[26].type.?, a27: P[27].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27 });
            }
        }.f,
        29 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?, a25: P[25].type.?, a26: P[26].type.?, a27: P[27].type.?, a28: P[28].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28 });
            }
        }.f,
        30 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?, a25: P[25].type.?, a26: P[26].type.?, a27: P[27].type.?, a28: P[28].type.?, a29: P[29].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29 });
            }
        }.f,
        31 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?, a25: P[25].type.?, a26: P[26].type.?, a27: P[27].type.?, a28: P[28].type.?, a29: P[29].type.?, a30: P[30].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30 });
            }
        }.f,
        32 => &struct {
            fn f(a0: P[0].type.?, a1: P[1].type.?, a2: P[2].type.?, a3: P[3].type.?, a4: P[4].type.?, a5: P[5].type.?, a6: P[6].type.?, a7: P[7].type.?, a8: P[8].type.?, a9: P[9].type.?, a10: P[10].type.?, a11: P[11].type.?, a12: P[12].type.?, a13: P[13].type.?, a14: P[14].type.?, a15: P[15].type.?, a16: P[16].type.?, a17: P[17].type.?, a18: P[18].type.?, a19: P[19].type.?, a20: P[20].type.?, a21: P[21].type.?, a22: P[22].type.?, a23: P[23].type.?, a24: P[24].type.?, a25: P[25].type.?, a26: P[26].type.?, a27: P[27].type.?, a28: P[28].type.?, a29: P[29].type.?, a30: P[30].type.?, a31: P[31].type.?) callconv(cc) R {
                return call(.{ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 });
            }
        }.f,
        else => @compileError("zsub: slots with more than 32 parameters are not supported"),
    };
}

test {
    _ = @import("tests.zig");
}
