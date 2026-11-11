// Native MKS reference; conventions adapted from ipole 7f7a482 (see LICENSE).
const std = @import("std");
pub const Vec = [4]f64;
pub const Mat = [4]Vec;
pub const Connection = [4]Mat;
pub const spin = 0.9375;
pub const hslope = 0.3;
pub const pi = std.math.pi;
pub const zero: Vec = @splat(0);

pub fn theta(x: f64) f64 {
    return pi * x + 0.5 * (1 - hslope) * @sin(2 * pi * x);
}

pub fn native(r: f64, degrees: f64, phi: f64) Vec {
    const target = degrees / 180 * pi;
    var lo: f64 = 0;
    var hi: f64 = 1;
    // Match the archived reference camera's stopping convention.
    for (0..1000) |_| {
        const mid = (lo + hi) / 2;
        if (@abs(theta(mid) - target) < 1e-9) return .{ 0, @log(r), mid, phi / 180 * pi };
        if (theta(mid) < target) lo = mid else hi = mid;
    }
    unreachable;
}

pub fn metric(x: Vec) Mat {
    const r = @exp(x[1]);
    const th = theta(x[2]);
    const s2 = @sin(th) * @sin(th);
    const rho2 = r * r + spin * spin * @cos(th) * @cos(th);
    const f = 2 * r / rho2;
    const d = pi * (1 + (1 - hslope) * @cos(2 * pi * x[2]));
    return .{
        .{ -1 + f, f * r, 0, -spin * f * s2 },
        .{ f * r, (1 + f) * r * r, 0, -spin * s2 * (1 + f) * r },
        .{ 0, 0, rho2 * d * d, 0 },
        .{ -spin * f * s2, -spin * s2 * (1 + f) * r, 0, s2 * (rho2 + spin * spin * s2 * (1 + f)) },
    };
}

pub fn inverse(g: Mat) !Mat {
    var a = g;
    var b: Mat = .{ zero, zero, zero, zero };
    for (0..4) |i| b[i][i] = 1;
    for (0..4) |i| {
        var pivot = i;
        for (i + 1..4) |j| {
            if (@abs(a[j][i]) > @abs(a[pivot][i])) pivot = j;
        }
        if (!std.math.isFinite(a[pivot][i]) or a[pivot][i] == 0) return error.SingularMetric;
        std.mem.swap(Vec, &a[i], &a[pivot]);
        std.mem.swap(Vec, &b[i], &b[pivot]);
        const p = a[i][i];
        for (0..4) |k| {
            a[i][k] /= p;
            b[i][k] /= p;
        }
        for (0..4) |j| {
            if (j == i) continue;
            const f = a[j][i];
            for (0..4) |k| {
                a[j][k] -= f * a[i][k];
                b[j][k] -= f * b[i][k];
            }
        }
    }
    return b;
}

pub fn mul(g: Mat, v: Vec) Vec {
    var out = zero;
    for (0..4) |i| for (0..4) |j| {
        out[i] += g[i][j] * v[j];
    };
    return out;
}

pub fn dot(a: Vec, g: Mat, b: Vec) f64 {
    var value: f64 = 0;
    for (0..4) |i| for (0..4) |j| {
        value += a[i] * b[j] * g[i][j];
    };
    return value;
}

pub fn normalize(v: Vec, g: Mat) !Vec {
    const norm = @sqrt(@abs(dot(v, g, v)));
    if (!std.math.isFinite(norm) or norm == 0) return error.DegenerateFrame;
    var out = v;
    for (&out) |*a| a.* /= norm;
    return out;
}

pub fn project(a: Vec, b: Vec, g: Mat) Vec {
    const factor = dot(a, g, b) / dot(b, g, b);
    var out = a;
    for (0..4) |i| out[i] -= factor * b[i];
    return out;
}

fn determinant(m: Mat) f64 {
    var det: f64 = 0;
    for (0..4) |i| for (0..4) |j| for (0..4) |k| for (0..4) |l| {
        const indices = [4]usize{ i, j, k, l };
        var sign: f64 = 1;
        for (0..4) |a| for (a + 1..4) |b| {
            if (indices[a] == indices[b]) sign = 0;
            if (indices[a] > indices[b]) sign = -sign;
        };
        det += sign * m[0][i] * m[1][j] * m[2][k] * m[3][l];
    };
    return det;
}

pub fn frame(u: Vec, k: Vec, b: Vec, g: Mat) !Mat {
    var e = Mat{ u, .{ 1, 1, 1, 1 }, b, k };
    e[0] = try normalize(e[0], g);
    for (0..2) |_| e[3] = project(e[3], e[0], g);
    e[3] = try normalize(e[3], g);
    for (0..2) |_| {
        e[2] = project(e[2], e[0], g);
        e[2] = project(e[2], e[3], g);
    }
    e[2] = try normalize(e[2], g);
    for (0..2) |_| for ([_]usize{ 0, 2, 3 }) |j| {
        e[1] = project(e[1], e[j], g);
    };
    e[1] = try normalize(e[1], g);
    if (determinant(e) < 0) for (&e[1]) |*v| {
        v.* = -v.*;
    };
    return e;
}

pub fn cameraFrame(x: Vec) !Mat {
    const g = metric(x);
    const inv = try inverse(g);
    return frame(mul(inv, .{ -1, 0, 0, 0 }), mul(inv, .{ 1, 1, 0, 0 }), .{ 0, 0, 1, 0 }, g);
}

pub fn cameraRay(e: Mat, i: usize, j: usize, nx: usize, ny: usize, fovx: f64, fovy: f64) Vec {
    const tx = ((@as(f64, @floatFromInt(i)) + 0.5 - 0.01) / @as(f64, @floatFromInt(nx)) - 0.5) * fovx;
    const ty = ((@as(f64, @floatFromInt(j)) + 0.5) / @as(f64, @floatFromInt(ny)) - 0.5) * fovy;
    const norm = @sqrt(1 + tx * tx + ty * ty);
    var k = zero;
    for (0..4) |a| k[a] = e[0][a] + (tx * e[1][a] + ty * e[2][a] + e[3][a]) / norm;
    return k;
}

pub fn connection(x: Vec) !Connection {
    const inv = try inverse(metric(x));
    var dg: Connection = @splat(.{ zero, zero, zero, zero });
    // Stationarity and axisymmetry make the other derivatives exactly zero.
    for (1..3) |k| {
        var hi = x;
        var lo = x;
        hi[k] += 1e-7;
        lo[k] -= 1e-7;
        const gh = metric(hi);
        const gl = metric(lo);
        for (0..4) |i| for (0..4) |j| {
            dg[k][i][j] = (gh[i][j] - gl[i][j]) / (hi[k] - lo[k]);
        };
    }
    var out: Connection = @splat(.{ zero, zero, zero, zero });
    for (0..4) |i| for (0..4) |j| for (0..4) |k| for (0..4) |l| {
        out[i][j][k] += 0.5 * inv[i][l] * (dg[k][l][j] + dg[j][l][k] - dg[l][j][k]);
    };
    return out;
}

pub fn transport(conn: Connection, v: Vec, k: Vec) Vec {
    var out = zero;
    for (0..4) |i| for (0..4) |j| for (0..4) |l| {
        out[i] -= conn[i][j][l] * v[j] * k[l];
    };
    return out;
}

pub const Ray = struct { x: Vec, k: Vec, f: Vec };

pub fn advance(ray: *Ray, dl: f64) !Ray {
    const conn = try connection(ray.x);
    const dk = transport(conn, ray.k, ray.k);
    const df = transport(conn, ray.f, ray.k);
    var mid = ray.*;
    for (0..4) |i| {
        mid.x[i] += dl * ray.k[i] / 2;
        mid.k[i] += dl * dk[i] / 2;
        mid.f[i] += dl * df[i] / 2;
    }
    const cm = try connection(mid.x);
    const dkm = transport(cm, mid.k, mid.k);
    const dfm = transport(cm, mid.f, mid.k);
    for (0..4) |i| {
        ray.x[i] += dl * mid.k[i];
        ray.k[i] += dl * dkm[i];
        ray.f[i] += dl * dfm[i];
        if (!std.math.isFinite(ray.x[i]) or !std.math.isFinite(ray.k[i]) or !std.math.isFinite(ray.f[i])) return error.NonfiniteRay;
    }
    return mid;
}

pub fn stepsize(ray: Ray, eps: f64) f64 {
    const deh = @min(@abs(ray.x[1]), 0.1);
    const pole = @min(@abs(ray.x[2]), @abs(1 - ray.x[2]));
    const fac = if (pole < 0.02) pole / 3 else @min(0.02 / 3.0 + (pole - 0.02) * 10, 1);
    return eps / ((@abs(ray.k[1]) + 1e-80) / (10 * deh) + (@abs(ray.k[2]) + 1e-80) / fac + @abs(ray.k[3]) + 1e-80);
}

test "native metric inverse and camera null/orthonormal frame" {
    const x = native(10000, 163, 0);
    const g = metric(x);
    const inv = try inverse(g);
    for (0..4) |i| for (0..4) |j| {
        var value: f64 = 0;
        for (0..4) |k| value += g[i][k] * inv[k][j];
        try std.testing.expectApproxEqAbs(@as(f64, if (i == j) 1 else 0), value, 1e-12);
    };
    const e = try cameraFrame(x);
    for (0..4) |i| for (0..4) |j| {
        try std.testing.expectApproxEqAbs(@as(f64, if (i != j) 0 else if (i == 0) -1 else 1), dot(e[i], g, e[j]), 1e-12);
    };
    const k = cameraRay(e, 0, 159, 160, 160, 0.02, 0.02);
    try std.testing.expectApproxEqAbs(@as(f64, 0), dot(k, g, k), 1e-12);
}

test "midpoint integration follows the exact ingoing principal null ray" {
    const x = Vec{ 0, @log(@as(f64, 20)), 0.4, 0.7 };
    var ray = Ray{ .x = x, .k = .{ 1, -0.05, 0, 0 }, .f = .{ 0, 0, 1 / @sqrt(metric(x)[2][2]), 0 } };
    for (0..1000) |_| _ = try advance(&ray, 0.001);
    try std.testing.expectApproxEqAbs(@as(f64, 19), @exp(ray.x[1]), 1e-7);
    try std.testing.expectApproxEqAbs(@as(f64, -1.0 / 19.0), ray.k[1], 1e-9);
    try std.testing.expectApproxEqAbs(@as(f64, 1), ray.k[0], 1e-9);
    const g = metric(ray.x);
    try std.testing.expectApproxEqAbs(@as(f64, 0), dot(ray.k, g, ray.k), 1e-9);
    try std.testing.expectApproxEqAbs(@as(f64, 1), dot(ray.f, g, ray.f), 1e-8);
    try std.testing.expectApproxEqAbs(@as(f64, 0), dot(ray.f, g, ray.k), 1e-9);
}
