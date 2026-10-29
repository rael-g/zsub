const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const zsub = b.addModule("zsub", .{ .root_source_file = b.path("src/zsub.zig"), .target = target, .optimize = optimize });

    const tests = b.addTest(.{ .root_module = zsub });
    b.step("test", "Run the zsub tests").dependOn(&b.addRunArtifact(tests).step);
}
