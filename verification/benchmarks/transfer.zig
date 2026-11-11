const std = @import("std");
pub const Vec = [4]f64;
pub const Mat = [4]Vec;
pub const Cell = struct { emission: Vec, transmission: Mat };

pub fn identity() Mat {
    var result: Mat = @splat(@splat(0));
    for (0..4) |i| result[i][i] = 1;
    return result;
}

pub fn multiply(a: Mat, b: Mat) Mat {
    var result: Mat = @splat(@splat(0));
    for (0..4) |i| for (0..4) |j| for (0..4) |k| {
        result[i][j] += a[i][k] * b[k][j];
    };
    return result;
}

pub fn apply(a: Mat, b: Vec) Vec {
    var result: Vec = @splat(0);
    for (0..4) |i| for (0..4) |j| {
        result[i] += a[i][j] * b[j];
    };
    return result;
}

/// Constant-cell affine exponential by a converged Taylor series and squaring.
/// The source is factored out so very large physical units don't drive scaling.
pub fn cell(j: Vec, a: Vec, r: [3]f64, ds: f64) !Cell {
    if (!std.math.isFinite(ds) or ds < 0) return error.InvalidCellLength;
    for (j ++ a) |v| if (!std.math.isFinite(v)) return error.NonfiniteCell;
    for (r) |v| if (!std.math.isFinite(v)) return error.NonfiniteCell;
    const ap = std.math.hypot(std.math.hypot(a[1], a[2]), a[3]);
    if (a[0] < ap or a[0] < 0) return error.NonpassiveAbsorption;
    var m: Mat = .{
        .{ -a[0], -a[1], -a[2], -a[3] },
        .{ -a[1], -a[0], -r[2], r[1] },
        .{ -a[2], r[2], -a[0], -r[0] },
        .{ -a[3], -r[1], r[0], -a[0] },
    };
    var norm: f64 = 0;
    for (&m) |*row| {
        var sum: f64 = 0;
        for (row) |*v| {
            v.* *= ds;
            sum += @abs(v.*);
        }
        norm = @max(norm, sum);
    }
    if (!std.math.isFinite(norm) or norm > 1e12) return error.CellTooLarge;
    var halvings: usize = 0;
    var scale: f64 = 1;
    while (norm * scale > 0.25) : (halvings += 1) scale /= 2;
    for (&m) |*row| for (row) |*v| {
        v.* *= scale;
    };
    var expm = identity();
    var term = identity();
    var phi = identity();
    for (1..19) |n| {
        term = multiply(term, m);
        for (0..4) |i| for (0..4) |k| {
            term[i][k] /= @floatFromInt(n);
            expm[i][k] += term[i][k];
            phi[i][k] += term[i][k] / @as(f64, @floatFromInt(n + 1));
        };
    }
    var emission = apply(phi, j);
    for (&emission) |*v| v.* *= ds * scale;
    for (0..halvings) |_| {
        const extra = apply(expm, emission);
        for (0..4) |i| emission[i] += extra[i];
        expm = multiply(expm, expm);
    }
    for (emission) |v| if (!std.math.isFinite(v)) return error.NonfiniteTransfer;
    return .{ .emission = emission, .transmission = expm };
}

pub fn solve(j: Vec, a: Vec, r: [3]f64, ds: f64, initial: Vec) !Vec {
    const c = try cell(j, a, r, ds);
    var result = apply(c.transmission, initial);
    for (0..4) |i| result[i] += c.emission[i];
    return result;
}

test "zero opacity, exact Faraday rotation, equilibrium, and cell composition" {
    const z: Vec = @splat(0);
    const s = Vec{ 1, 0.2, 0.3, 0.1 };
    const free = try solve(.{ 2, 0, 0, 0 }, z, .{ 0, 0, 0 }, 0.5, s);
    try std.testing.expectApproxEqAbs(@as(f64, 2), free[0], 1e-14);
    const rotation = try solve(z, z, .{ 0, 0, 30 }, 1, s);
    try std.testing.expectApproxEqAbs(@cos(@as(f64, 30)) * s[1] - @sin(@as(f64, 30)) * s[2], rotation[1], 1e-13);
    try std.testing.expectApproxEqAbs(@sin(@as(f64, 30)) * s[1] + @cos(@as(f64, 30)) * s[2], rotation[2], 1e-13);
    const equilibrium = try solve(.{ 30, 9, 6, -3 }, .{ 100, 30, 20, -10 }, .{ 0, 0, 0 }, 1, z);
    for (equilibrium, Vec{ 0.3, 0, 0, 0 }) |actual, expected| try std.testing.expectApproxEqAbs(expected, actual, 1e-13);
    const j = Vec{ 2, 0.1, 0.2, 0 };
    const a = Vec{ 1, 0.2, 0.1, 0 };
    const r = [3]f64{ 2, 3, 4 };
    const full = try solve(j, a, r, 1, s);
    const halves = try solve(j, a, r, 0.5, try solve(j, a, r, 0.5, s));
    for (full, halves) |v, w| try std.testing.expectApproxEqAbs(v, w, 1e-13);
    try std.testing.expectError(error.InvalidCellLength, cell(j, a, r, -1));
    try std.testing.expectError(error.NonpassiveAbsorption, cell(j, .{ 0, 1, 0, 0 }, r, 1));
    try std.testing.expectError(error.NonpassiveAbsorption, cell(j, .{ 1e-200, 1e-200, 1e-200, 0 }, r, 1));
}
