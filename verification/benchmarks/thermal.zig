// Dexter/Shcherbakov thermal fits, adapted from ipole 7f7a482 (see LICENSE).
const std = @import("std");
const units = @import("snapshot.zig");
const pi: f64 = std.math.pi;
const ee: f64 = 4.80320680e-10;
// Retain the archived GSL binary32 underflow convention without linking GSL.
pub const cold_threshold: f32 = 0.0013475478626787663;

fn pow(x: f64, y: f64) f64 {
    return std.math.pow(f64, x, y);
}

/// K_n(z) = integral exp(-z cosh(t)) cosh(n t) dt, n = 0,1,2.
/// Scaling by exp(z) keeps the quadrature finite in the cold regime.
pub fn besselScaled(z: f64, panels: usize) [3]f64 {
    const stop = std.math.acosh(1 + 60 / z);
    const h = stop / @as(f64, @floatFromInt(panels));
    var sums: [3]f64 = @splat(0);
    for (0..panels + 1) |i| {
        const t = h * @as(f64, @floatFromInt(i));
        const e = @exp(t);
        const c = (e + 1 / e) / 2;
        const weight: f64 = if (i == 0 or i == panels) 1 else if (i % 2 == 0) 2 else 4;
        const v = weight * @exp(-z * (c - 1));
        sums[0] += v;
        sums[1] += v * c;
        sums[2] += v * (2 * c * c - 1);
    }
    for (&sums) |*v| v.* *= h / 3;
    return sums;
}

pub fn ratios(temperature: f64) [2]f64 {
    if (temperature < cold_threshold) return .{ 1, 1 };
    const k = besselScaled(1 / temperature, 512);
    return .{ k[0] / k[2], k[1] / k[2] };
}

pub fn coefficients(q: [5]f64, kr: [2]f64) ![12]f64 {
    const ne, const t, const b, const nu, const mu = q;
    for (q) |v| if (!std.math.isFinite(v)) return error.NonfiniteThermalInput;
    if (ne < 0 or b < 0 or t < 0.001 or t > 1000 or nu < 1e8 or nu > @as(f64, @as(f32, 1e20)) or @abs(mu) > 1) return error.ThermalInputOutsideDomain;
    var row: [12]f64 = @splat(0);
    row[11] = 1;
    if (ne == 0 or b == 0) return row;
    const angle = std.math.acos(mu);
    const sine = @sin(angle);
    const cosine = @cos(angle);
    const omega0 = ee * b / (units.me * units.cl);
    const wp2 = 4 * pi * ne * ee * ee / units.me;
    const x = t * @sqrt(@sqrt(@as(f64, 2)) * sine * (1e3 * omega0 / (2 * pi * nu)));
    if (@abs(mu) < 1) {
        const nus = 3 * ee * b * sine / 4 / pi / units.me / units.cl * t * t + 1;
        const y = nu / nus;
        const e = @exp(-1.8899 * pow(y, 1.0 / 3.0));
        const ym1 = pow(y, -1.0 / 3.0);
        const ym2 = pow(y, -2.0 / 3.0);
        const prefactor = ne * ee * ee * nu / 2 / @sqrt(@as(f64, 3)) / units.cl / t / t;
        row[0] = prefactor * 2.5651 * (1 + 1.92 * ym1 + 0.9977 * ym2) * e;
        row[1] = prefactor * 2.5651 * (1 + 0.93193 * ym1 + 0.499873 * ym2) * e;
        row[3] = 2 * ne * ee * ee * nu / @tan(angle) / 3 / @sqrt(@as(f64, 3)) / units.cl / t / t / t * (1.81384 / y + 3.42319 * ym2 + 0.0292545 * pow(y, -0.5) + 2.03773 * ym1) * e;
        // A scaled norm preserves the 0.99 cap for subnormal emissivities.
        const jp = std.math.hypot(row[1], row[3]);
        if (jp > row[0] * 0.99) {
            row[1] *= row[0] * 0.99 / jp;
            row[3] *= row[0] * 0.99 / jp;
        }
        const planck_x = units.hpl * nu / (units.me * units.cl * units.cl * t);
        const denom = if (planck_x < 2e-3) planck_x / 24 * (24 + planck_x * (12 + planck_x * (4 + planck_x))) else @exp(planck_x) - 1;
        const planck = (2 * units.hpl / (units.cl * units.cl)) / denom * pow(nu, 3);
        if (planck > 0) for (0..4) |i| {
            row[i + 4] = row[i] / planck * units.length;
        };
        const extra = (0.011 * @exp(-x / 47.2) - pow(2, -1.0 / 3.0) / pow(3, 23.0 / 6.0) * pi * 1e4 * pow(x + 1e-16, -8.0 / 3.0)) * (0.5 + 0.5 * std.math.tanh((@log(x) - @log(@as(f64, 120))) / 0.1));
        const jf = 2.011 * @exp(-pow(x, 1.035) / 4.7) - @cos(x / 2) * @exp(-pow(x, 1.2) / 2.73) - 0.011 * @exp(-x / 47.2) + extra;
        const eps = jf * wp2 * pow(omega0, 2) / pow(2 * pi * nu, 4) * (kr[1] + 6 * t) * sine * sine;
        row[8] = 2 * pi * nu / (2 * units.cl) * eps * units.length;
    }
    const fit = kr[0] * (1 - 0.11 * @log(1 + 0.035 * x));
    row[10] = 2 * pi * nu / units.cl * (wp2 * omega0 / pow(2 * pi * nu, 3) * fit * cosine) * units.length;
    const redshift = 2.3e11 / nu;
    for (0..4) |i| row[i] *= units.length * redshift * redshift * redshift;
    for (row) |v| if (!std.math.isFinite(v)) return error.NonfiniteCoefficient;
    return row;
}

pub const Table = struct {
    pub const logmin = @log(@as(f64, 0.002));
    pub const step = (@log(@as(f64, 1000)) - logmin) / 8192;
    values: [8193][2]f64,

    pub fn init() Table {
        var table: Table = undefined;
        for (&table.values, 0..) |*v, i| v.* = ratios(@exp(logmin + @as(f64, @floatFromInt(i)) * step));
        return table;
    }

    pub fn lookup(self: *const Table, t: f64) [2]f64 {
        if (t < 0.002) return ratios(t);
        const index = std.math.clamp((@log(t) - logmin) / step, 0, 8192);
        const lo: usize = @min(@as(usize, @intFromFloat(index)), 8191);
        const f = index - @as(f64, @floatFromInt(lo));
        return .{ self.values[lo][0] * (1 - f) + self.values[lo + 1][0] * f, self.values[lo][1] * (1 - f) + self.values[lo + 1][1] * f };
    }
};

test "Bessel integral known values, recurrence, and quadrature refinement" {
    const expected = [3]f64{ 0.42102443824070833, 0.6019072301972346, 1.6248388986351774 };
    const k = besselScaled(1, 512);
    for (k, expected) |actual, reference| try std.testing.expectApproxEqRel(reference, actual / @exp(@as(f64, 1)), 1e-12);
    for ([_]f64{ 0.001, 1, 500, 1000 }) |z| {
        const a = besselScaled(z, 512);
        const b = besselScaled(z, 1024);
        for (a, b) |v, w| try std.testing.expectApproxEqRel(w, v, 1e-11);
        try std.testing.expectApproxEqRel(a[0] + 2 / z * a[1], a[2], 1e-11);
    }
}

test "thermal zero field, bounds, and emission polarization" {
    const zero = try coefficients(.{ 1e4, 1, 0, 2.3e11, 0 }, ratios(1));
    for (zero[0..11]) |v| try std.testing.expectEqual(@as(f64, 0), v);
    try std.testing.expectError(error.ThermalInputOutsideDomain, coefficients(.{ 1e4, 1, 10, 2.3e11, 2 }, ratios(1)));
    const row = try coefficients(.{ 1e4, 10, 10, 2.3e11, 0.3 }, ratios(10));
    try std.testing.expect(row[0] > 0);
    try std.testing.expect(@sqrt(row[1] * row[1] + row[3] * row[3]) <= row[0] * 0.99000000001);
    const faint = try coefficients(.{ 121.87877655029297, 0.41529738903045654, 0.7093679904937744, 4794281885696.0, -0.9774677157402039 }, ratios(0.41529738903045654));
    try std.testing.expect(faint[0] > 0 and faint[0] < 1e-200);
    try std.testing.expect(std.math.hypot(faint[1], faint[3]) <= faint[0] * 0.99000000001);
}
