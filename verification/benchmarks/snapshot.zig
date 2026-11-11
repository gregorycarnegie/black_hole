const std = @import("std");
const geo = @import("geometry.zig");
pub const cl: f64 = 2.99792458e10;
pub const mp: f64 = 1.67262171e-24;
pub const me: f64 = 9.1093826e-28;
pub const hpl: f64 = 6.6260693e-27;
pub const length: f64 = 6.6742e-8 * 6.2e9 * 1.989e33 / (cl * cl);
pub const density_unit: f64 = 1.672e26 / (length * length * length);
pub const field_unit: f64 = cl * @sqrt(4 * std.math.pi * density_unit);
pub const grid = [3]usize{ 288, 128, 128 };
pub const start = [3]f64{ 0.16356844652525657, 0, 0 };
pub const dx = [3]f64{ 0.023417315390475278, 0.0078125, 0.04908738521234052 };
const cell_count = grid[0] * grid[1] * grid[2];
pub const default_path = "target/eht-benchmark/sample_dump_SANE_a+0.94_MKS_0900.h5";

pub fn readFloat(comptime T: type, bytes: []const u8) T {
    const Int = if (T == f32) u32 else u64;
    return @bitCast(std.mem.readInt(Int, bytes[0..@sizeOf(T)], .little));
}

pub fn fourVectors(p: [8]f64, g: geo.Mat, inv: geo.Mat) struct { u: geo.Vec, b: geo.Vec } {
    var v2: f64 = 0;
    for (1..4) |i| for (1..4) |j| {
        v2 += g[i][j] * p[i + 1] * p[j + 1];
    };
    const fac = @sqrt(-(1 + @abs(v2)) / inv[0][0]);
    var u: geo.Vec = .{ -fac * inv[0][0], 0, 0, 0 };
    for (1..4) |i| u[i] = p[i + 1] - fac * inv[0][i];
    const ucov = geo.mul(g, u);
    var b = geo.zero;
    for (1..4) |i| b[0] += ucov[i] * p[i + 4];
    for (1..4) |i| b[i] = (p[i + 4] + u[i] * b[0]) / u[0];
    return .{ .u = u, .b = b };
}

pub fn temperature(rho: f64, energy: f64, bsq: f64) f64 {
    const beta = 2 * energy * (1.444444 - 1) / bsq;
    const beta2 = beta * beta;
    const trat = 3 * beta2 / (1 + beta2) + 3 / (1 + beta2);
    const game = 1.333333333333333;
    const gamp = 1.666666666666667;
    const scale = mp / me * (game - 1) * (gamp - 1) / ((gamp - 1) + (game - 1) * trat);
    const t = scale * energy / rho;
    return if (std.math.isNan(t)) 1e-3 else @max(t, 1e-3);
}

pub const Snapshot = struct {
    raw: []u8,
    physical: [][4]f64,
    allocator: std.mem.Allocator,

    pub fn load(io: std.Io, allocator: std.mem.Allocator, path: []const u8) !Snapshot {
        const raw = try std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(302010649));
        errdefer allocator.free(raw);
        try validate(raw);
        const physical = try allocator.alloc([4]f64, cell_count);
        errdefer allocator.free(physical);
        var self = Snapshot{ .raw = raw, .physical = physical, .allocator = allocator };
        for (0..grid[0]) |i| for (0..grid[1]) |j| {
            const x = geo.Vec{ 0, start[0] + (@as(f64, @floatFromInt(i)) + 0.5) * dx[0], (@as(f64, @floatFromInt(j)) + 0.5) * dx[1], 0 };
            const g = geo.metric(x);
            const inv = try geo.inverse(g);
            for (0..grid[2]) |k| {
                const index = (i * grid[1] + j) * grid[2] + k;
                const p = self.primitive(index);
                for (p) |value| if (!std.math.isFinite(value)) return error.NonfinitePrimitive;
                if (p[0] <= 0 or p[1] <= 0) return error.NonpositivePrimitive;
                const vectors = fourVectors(p, g, inv);
                // Preserve the reference's conversion through gauss before sigma/beta.
                const field = @sqrt(geo.dot(vectors.b, g, vectors.b)) * field_unit;
                const code_b = field / field_unit;
                const bsq = code_b * code_b;
                if (!std.math.isFinite(field)) return error.InvalidMagneticNorm;
                physical[index] = .{ p[0] * density_unit / (mp + me), temperature(p[0], p[1], bsq), field, @max(bsq / p[0], 1e-40) };
            }
        };
        return self;
    }

    pub fn deinit(self: *Snapshot) void {
        self.allocator.free(self.physical);
        self.allocator.free(self.raw);
    }

    pub fn primitive(self: Snapshot, index: usize) [8]f64 {
        var p: [8]f64 = undefined;
        for (&p, 0..) |*v, n| v.* = readFloat(f32, self.raw[16664 + (index * 8 + n) * 4 ..]);
        return p;
    }

    fn cell(i: isize, j: isize, k: isize) usize {
        const ii: usize = @intCast(std.math.clamp(i, 0, grid[0] - 1));
        const jj: usize = @intCast(std.math.clamp(j, 0, grid[1] - 1));
        const kk: usize = @intCast(@mod(k + @as(isize, if (j < 0 or j >= grid[1]) grid[2] / 2 else 0), grid[2]));
        return (ii * grid[1] + jj) * grid[2] + kk;
    }

    pub fn sample(self: Snapshot, x: geo.Vec) ![40]f64 {
        for (x) |v| if (!std.math.isFinite(v)) return error.NonfiniteQuery;
        if (x[1] < start[0] or x[1] >= start[0] + grid[0] * dx[0] or x[2] <= 0 or x[2] >= 1) return error.QueryOutsideGrid;
        const pos = [3]f64{ x[1], x[2], @mod(x[3], 2 * std.math.pi) };
        var base: [3]isize = undefined;
        var d: [3]f64 = undefined;
        for (0..3) |n| {
            base[n] = @intFromFloat(std.math.clamp(@floor((pos[n] - start[n]) / dx[n] - 0.5), -1, @as(f64, @floatFromInt(grid[n] - 1))));
            d[n] = std.math.clamp((pos[n] - (start[n] + (@as(f64, @floatFromInt(base[n])) + 0.5) * dx[n])) / dx[n], 0, 1);
        }
        var row: [40]f64 = @splat(0);
        for (0..2) |k| for (0..2) |j| for (0..2) |i| {
            const index = cell(base[0] + @as(isize, @intCast(i)), base[1] + @as(isize, @intCast(j)), base[2] + @as(isize, @intCast(k)));
            const w = (if (i == 0) 1 - d[0] else d[0]) * (if (j == 0) 1 - d[1] else d[1]) * (if (k == 0) 1 - d[2] else d[2]);
            const p = self.primitive(index);
            for (0..8) |n| row[n] += w * p[n];
            for (0..4) |n| row[16 + n] += w * self.physical[index][n];
        };
        if (row[19] >= 1) row[16] = 0;
        const g = geo.metric(x);
        const vectors = fourVectors(row[0..8].*, g, try geo.inverse(g));
        row[8..12].* = vectors.u;
        row[12..16].* = vectors.b;
        for (0..4) |i| for (0..4) |j| {
            row[20 + i * 4 + j] = g[i][j];
        };
        const r = @exp(x[1]);
        const th = geo.theta(x[2]);
        row[36] = (r * @cos(x[3]) - geo.spin * @sin(x[3])) * @sin(th);
        row[37] = r * @cos(th);
        row[38] = -(r * @sin(x[3]) + geo.spin * @cos(x[3])) * @sin(th);
        row[39] = if (r > 1 and r < 100 and th > 0.0174 and th < std.math.pi - 0.0174) 1 else 0;
        return row;
    }
};

pub fn validate(raw: []const u8) !void {
    if (raw.len != 302010648) return error.SnapshotSizeMismatch;
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(raw, &digest, .{});
    var expected: [32]u8 = undefined;
    _ = std.fmt.hexToBytes(&expected, "c2d1dfdc8c92320ec77d22953f55c2b5d71b685496f5199c73a1280f20a0d537") catch unreachable;
    if (!std.mem.eql(u8, &digest, &expected)) return error.SnapshotHashMismatch;
    // shortcut: offsets are valid only for this SHA-256-pinned, contiguous HDF5
    // snapshot; add a general HDF5 reader when supporting another input file.
    if (readFloat(f64, raw[2536..]) != 4501.677840911209 or readFloat(f64, raw[2524..]) != geo.spin or readFloat(f64, raw[2516..]) != geo.hslope) return error.SnapshotHeaderMismatch;
}

test "snapshot rejects substituted data and retains zero-field temperature floor" {
    try std.testing.expectError(error.SnapshotSizeMismatch, validate(""));
    try std.testing.expectEqual(@as(f64, 1e-3), temperature(1, 1, 0));
    try std.testing.expectApproxEqRel(mp / me * 2 / 15, temperature(1, 1, 1), 1e-14);
    try std.testing.expectEqual(@as(usize, (0 * 128 + 0) * 128 + 64), Snapshot.cell(-1, -1, 0));
    try std.testing.expectEqual(Snapshot.cell(0, 0, 127), Snapshot.cell(0, 0, -1));
}
