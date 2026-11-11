//! Standalone binary64 EHT reference. No libc, C sources, GSL or HDF5 library.
const std = @import("std");
const geo = @import("geometry.zig");
const snapshot = @import("snapshot.zig");
const thermal = @import("thermal.zig");
const transfer = @import("transfer.zig");
const Allocator = std.mem.Allocator;

const Config = struct {
    dump: []const u8 = snapshot.default_path,
    outfile: []const u8 = "target/eht-benchmark/zig-reference.f64",
    nx: usize = 160,
    ny: usize = 160,
    rcam: f64 = 10000,
    thetacam: f64 = 163,
    phicam: f64 = 0,
    fovx_dsource: f64 = 160,
    fovy_dsource: f64 = 160,
    dsource: f64 = 16.9e6,
    freqcgs: f64 = 230e9,
    eps: f64 = 0.01,

    fn parse(text: []const u8) !Config {
        var config = Config{};
        var lines = std.mem.splitScalar(u8, text, '\n');
        while (lines.next()) |line| {
            var words = std.mem.tokenizeAny(u8, line[0 .. std.mem.indexOfScalar(u8, line, '#') orelse line.len], " \t\r");
            const key = words.next() orelse continue;
            const value = words.next() orelse return error.MissingParameterValue;
            if (words.next() != null) return error.ExtraParameterValue;
            var handled = false;
            inline for (@typeInfo(Config).@"struct".field_names, @typeInfo(Config).@"struct".field_types) |name, Field| {
                if (std.mem.eql(u8, key, name)) {
                    @field(config, name) = if (Field == []const u8) value else if (Field == usize) try std.fmt.parseInt(usize, value, 10) else try std.fmt.parseFloat(f64, value);
                    handled = true;
                }
            }
            if (handled) continue;
            const fixed = .{ .{ "MBH", @as(f64, 6.2e9) }, .{ "M_unit", @as(f64, 1.672e26) }, .{ "trat_small", @as(f64, 3) }, .{ "trat_large", @as(f64, 3) }, .{ "beta_crit", @as(f64, 1) }, .{ "sigma_cut", @as(f64, 1) }, .{ "rotcam", @as(f64, 0) }, .{ "qu_conv", @as(f64, 0) }, .{ "only_unpolarized", @as(f64, 0) }, .{ "quench_output", @as(f64, 0) }, .{ "add_ppm", @as(f64, 0) } };
            inline for (fixed) |pair| {
                if (std.mem.eql(u8, key, pair[0])) {
                    if (try std.fmt.parseFloat(f64, value) != pair[1]) return error.UnsupportedBenchmarkParameter;
                    handled = true;
                }
            }
            if (!handled) return error.UnknownParameter;
        }
        inline for (@typeInfo(Config).@"struct".field_names, @typeInfo(Config).@"struct".field_types) |name, Field| {
            if (Field == f64 and !std.math.isFinite(@field(config, name))) return error.NonfiniteParameter;
        }
        if (config.nx == 0 or config.ny == 0 or config.nx > 4096 or config.ny > 4096 or config.rcam <= 100 or config.thetacam <= 0 or config.thetacam >= 180 or config.eps <= 0 or config.eps > 0.02 or config.dsource <= 0 or config.fovx_dsource <= 0 or config.fovy_dsource <= 0 or config.freqcgs != 230e9) return error.InvalidBenchmarkParameter;
        return config;
    }

    fn fov(self: Config) [2]f64 {
        const factor = (self.dsource * 3.085678e18) / snapshot.length / 2.06265e11 / self.rcam;
        return .{ self.fovx_dsource * factor, self.fovy_dsource * factor };
    }

    fn jyScale(self: Config) f64 {
        return (self.fovx_dsource / 2.06265e11 / @as(f64, @floatFromInt(self.nx))) * (self.fovy_dsource / 2.06265e11 / @as(f64, @floatFromInt(self.ny))) / 1e-23;
    }
};

fn read(io: std.Io, allocator: Allocator, path: []const u8) ![]u8 {
    return std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(1024 * 1024 * 1024));
}

fn writeFloats(comptime T: type, io: std.Io, allocator: Allocator, path: []const u8, values: []const T) !void {
    const bytes = try allocator.alloc(u8, values.len * @sizeOf(T));
    defer allocator.free(bytes);
    const Int = if (T == f32) u32 else u64;
    for (values, 0..) |v, i| std.mem.writeInt(Int, bytes[i * @sizeOf(T) ..][0..@sizeOf(T)], @bitCast(v), .little);
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = path, .data = bytes });
}

fn queries(comptime width: usize, bytes: []const u8, offset: usize) ![width]f64 {
    if (bytes.len % (width * 8) != 0) return error.TruncatedQueryRecord;
    var row: [width]f64 = undefined;
    for (&row, 0..) |*v, i| v.* = snapshot.readFloat(f64, bytes[offset + i * 8 ..]);
    return row;
}

fn sampleProbe(io: std.Io, allocator: Allocator, config: Config, input: []const u8, output: []const u8) !void {
    const bytes = try read(io, allocator, input);
    defer allocator.free(bytes);
    if (bytes.len % 24 != 0) return error.TruncatedQueryRecord;
    var model = try snapshot.Snapshot.load(io, allocator, config.dump);
    defer model.deinit();
    const result = try allocator.alloc(f64, bytes.len / 24 * 40);
    defer allocator.free(result);
    for (0..bytes.len / 24) |n| {
        const q = try queries(3, bytes, n * 24);
        const row = try model.sample(.{ 4501.677840911209, q[0], q[1], q[2] });
        @memcpy(result[n * 40 ..][0..40], &row);
    }
    try writeFloats(f64, io, allocator, output, result);
}

fn thermalProbe(io: std.Io, allocator: Allocator, input: []const u8, output: []const u8, table_path: []const u8) !void {
    const bytes = try read(io, allocator, input);
    defer allocator.free(bytes);
    if (bytes.len % 40 != 0) return error.TruncatedQueryRecord;
    const result = try allocator.alloc(f64, bytes.len / 40 * 12);
    defer allocator.free(result);
    for (0..bytes.len / 40) |i| {
        const q = try queries(5, bytes, i * 40);
        const row = try thermal.coefficients(q, thermal.ratios(q[1]));
        @memcpy(result[i * 12 ..][0..12], &row);
    }
    const table = try allocator.create(thermal.Table);
    defer allocator.destroy(table);
    table.* = thermal.Table.init();
    var payload: [4 + 8193 * 2]f32 = undefined;
    payload[0..4].* = .{ @floatCast(thermal.Table.logmin), @floatCast(thermal.Table.step), thermal.cold_threshold, 1000 };
    for (table.values, 0..) |v, i| {
        payload[4 + 2 * i] = @floatCast(v[0]);
        payload[5 + 2 * i] = @floatCast(v[1]);
    }
    try writeFloats(f64, io, allocator, output, result);
    try writeFloats(f32, io, allocator, table_path, &payload);
}

fn cameraProbe(io: std.Io, allocator: Allocator, config: Config, output: []const u8) !void {
    const x = geo.native(config.rcam, config.thetacam, config.phicam);
    const frame = try geo.cameraFrame(x);
    const fov = config.fov();
    const result = try allocator.alloc(f64, config.nx * config.ny * 24);
    defer allocator.free(result);
    for (0..config.nx) |i| for (0..config.ny) |j| {
        const row = result[(i * config.ny + j) * 24 ..][0..24];
        @memcpy(row[0..4], &x);
        const k = geo.cameraRay(frame, i, j, config.nx, config.ny, fov[0], fov[1]);
        @memcpy(row[4..8], &k);
        for (frame, 0..) |v, a| @memcpy(row[8 + 4 * a ..][0..4], &v);
    };
    try writeFloats(f64, io, allocator, output, result);
}

fn initialRay(config: Config, frame: geo.Mat, i: usize, j: usize) !geo.Ray {
    const x = geo.native(config.rcam, config.thetacam, config.phicam);
    const fov = config.fov();
    const k = geo.cameraRay(frame, i, j, config.nx, config.ny, fov[0], fov[1]);
    var n = k;
    for (0..4) |a| n[a] -= frame[0][a];
    return .{ .x = x, .k = k, .f = try geo.normalize(geo.project(frame[1], n, geo.metric(x)), geo.metric(x)) };
}

fn outerProbe(io: std.Io, allocator: Allocator, config: Config, output: []const u8) !void {
    const x = geo.native(config.rcam, config.thetacam, config.phicam);
    const frame = try geo.cameraFrame(x);
    var result: [16 * 12]f64 = undefined;
    for (0..16) |pixel| {
        const index = pixel * (config.nx * config.ny - 1) / 15;
        var ray = try initialRay(config, frame, index / config.ny, index % config.ny);
        var iteration: usize = 0;
        while (@exp(ray.x[1]) > 120 + 1e-8) : (iteration += 1) {
            if (iteration == 100000) return error.OuterStepBudgetExceeded;
            const r = @exp(ray.x[1]);
            const dl = @min(geo.stepsize(ray, 0.000125), (r - 120) / (1.1 * @abs(r * ray.k[1])));
            _ = try geo.advance(&ray, -dl);
        }
        @memcpy(result[pixel * 12 ..][0..4], &ray.x);
        @memcpy(result[pixel * 12 + 4 ..][0..4], &ray.k);
        @memcpy(result[pixel * 12 + 8 ..][0..4], &ray.f);
    }
    try writeFloats(f64, io, allocator, output, &result);
}

fn imageCoefficients(model: snapshot.Snapshot, table: *const thermal.Table, mid: geo.Ray) ![12]f64 {
    const r = @exp(mid.x[1]);
    const th = geo.theta(mid.x[2]);
    if (r <= 1 or r >= 100 or th <= 0.0174 or th >= std.math.pi - 0.0174 or mid.x[1] < snapshot.start[0] or mid.x[1] >= snapshot.start[0] + 288 * snapshot.dx[0]) return @splat(0);
    const sample = try model.sample(mid.x);
    if (sample[16] == 0 or sample[18] == 0) return @splat(0);
    const g = geo.metric(mid.x);
    const u = sample[8..12].*;
    const b = sample[12..16].*;
    const energy = -geo.dot(u, g, mid.k);
    const bnorm = @sqrt(@abs(geo.dot(b, g, b)));
    const mu = std.math.clamp(geo.dot(b, g, mid.k) / (energy * bnorm), -1, 1);
    const t = sample[17];
    var row = try thermal.coefficients(.{ sample[16], t, sample[18], 230e9 * energy, mu }, table.lookup(t));
    if (@abs(mu) == 1) {
        row[11] = energy;
        return row;
    }
    // The transported first screen is gauged into the fluid rest frame.
    var screen = mid.f;
    const gauge = geo.dot(u, g, screen) / energy;
    for (0..4) |i| screen[i] += gauge * mid.k[i];
    screen = try geo.normalize(screen, g);
    const e = try geo.frame(u, mid.k, b, g);
    const c = geo.dot(screen, g, e[1]);
    const s = geo.dot(screen, g, e[2]);
    const c2 = c * c - s * s;
    const s2 = -2 * c * s;
    for ([_]usize{ 0, 4, 8 }) |offset| {
        const q = row[if (offset == 8) 8 else offset + 1];
        if (offset == 8) {
            row[8] = q * c2;
            row[9] = q * s2;
        } else {
            row[offset + 1] = q * c2;
            row[offset + 2] = q * s2;
        }
    }
    row[11] = energy;
    return row;
}

fn image(io: std.Io, allocator: Allocator, config: Config, output: []const u8, stride: usize) !void {
    if (stride == 0 or stride > @min(config.nx, config.ny)) return error.InvalidStride;
    var model = try snapshot.Snapshot.load(io, allocator, config.dump);
    defer model.deinit();
    const table = try allocator.create(thermal.Table);
    defer allocator.destroy(table);
    table.* = thermal.Table.init();
    const x = geo.native(config.rcam, config.thetacam, config.phicam);
    const frame = try geo.cameraFrame(x);
    const nx = (config.nx + stride - 1) / stride;
    const ny = (config.ny + stride - 1) / stride;
    const result = try allocator.alloc(f64, nx * ny * 4);
    defer allocator.free(result);
    var totals = geo.zero;
    var max_steps: usize = 0;
    var max_null: f64 = 0;
    for (0..nx) |ii| {
        for (0..ny) |jj| {
            var ray = try initialRay(config, frame, ii * stride, jj * stride);
            var emission = geo.zero;
            var foreground = transfer.identity();
            var steps: usize = 0;
            while (true) : (steps += 1) {
                const r = @exp(ray.x[1]);
                if (r < 1 + @sqrt(1 - geo.spin * geo.spin) + 0.0001 or (r > 100 and ray.k[1] < 0)) break;
                if (steps == 100000) return error.ImageStepBudgetExceeded;
                const dl = geo.stepsize(ray, config.eps);
                if (!std.math.isFinite(dl) or dl <= 0) return error.InvalidStep;
                const mid = try geo.advance(&ray, -dl);
                const coeff = try imageCoefficients(model, table, mid);
                if (coeff[0] > 0 or coeff[4] > 0 or coeff[10] != 0) {
                    const cell = transfer.cell(coeff[0..4].*, coeff[4..8].*, coeff[8..11].*, dl * coeff[11]) catch |err| {
                        std.debug.print("pixel ({d},{d}), absorption {any}, radius {d}: {s}\n", .{ ii * stride, jj * stride, coeff[4..8].*, @exp(mid.x[1]), @errorName(err) });
                        return err;
                    };
                    const source = transfer.apply(foreground, cell.emission);
                    for (0..4) |i| emission[i] += source[i];
                    foreground = transfer.multiply(foreground, cell.transmission);
                }
            }
            max_steps = @max(max_steps, steps);
            max_null = @max(max_null, @abs(geo.dot(ray.k, geo.metric(ray.x), ray.k)));
            // Project the transverse coherency onto the fixed camera axes.
            const initial = try initialRay(config, frame, ii * stride, jj * stride);
            const g = geo.metric(x);
            var n = initial.k;
            for (0..4) |i| n[i] -= frame[0][i];
            const f2 = try geo.normalize(geo.project(geo.project(frame[2], n, g), initial.f, g), g);
            const a = geo.dot(initial.f, g, frame[1]);
            const b = geo.dot(f2, g, frame[1]);
            const c = geo.dot(initial.f, g, frame[2]);
            const d = geo.dot(f2, g, frame[2]);
            const xx = ((a * a + b * b) * emission[0] + (a * a - b * b) * emission[1]) / 2 + a * b * emission[2];
            const yy = ((c * c + d * d) * emission[0] + (c * c - d * d) * emission[1]) / 2 + c * d * emission[2];
            const value = geo.Vec{ xx + yy, -(xx - yy), -((a * c + b * d) * emission[0] + (a * c - b * d) * emission[1] + (a * d + b * c) * emission[2]), (a * d - b * c) * emission[3] };
            for (value, 0..) |v, i| {
                if (!std.math.isFinite(v)) return error.NonfiniteImage;
                result[(ii * ny + jj) * 4 + i] = v * config.jyScale();
                totals[i] += v * config.jyScale();
            }
        }
        std.debug.print("reference row {d}/{d}\n", .{ ii + 1, nx });
    }
    try writeFloats(f64, io, allocator, output, result);
    const meta_path = try std.fmt.allocPrint(allocator, "{s}.json", .{output});
    defer allocator.free(meta_path);
    const meta = try std.fmt.allocPrint(allocator, "{{\n  \"solver\": \"standalone Zig MKS midpoint / full polarized affine transfer\",\n  \"snapshot_sha256\": \"c2d1dfdc8c92320ec77d22953f55c2b5d71b685496f5199c73a1280f20a0d537\",\n  \"shape\": [{d}, {d}, 4],\n  \"stride\": {d},\n  \"eps\": {d},\n  \"Jy_per_CGS_intensity\": {d},\n  \"summed_stokes_Jy\": [{d}, {d}, {d}, {d}],\n  \"max_steps\": {d},\n  \"max_absolute_null_residual\": {d},\n  \"scope\": \"finite numerical reference; convergence and physical accuracy require assessment\"\n}}\n", .{ nx, ny, stride, config.eps, config.jyScale(), totals[0], totals[1], totals[2], totals[3], max_steps, max_null });
    defer allocator.free(meta);
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = meta_path, .data = meta });
}

pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    const args = try init.minimal.args.toSlice(allocator);
    const io = init.io;
    if (args.len == 5 and std.mem.eql(u8, args[1], "thermal")) return thermalProbe(io, allocator, args[2], args[3], args[4]);
    if (args.len < 4) return error.UsageReferenceModeParameterFileOutput;
    const text = try read(io, allocator, args[2]);
    const config = try Config.parse(text);
    const mode = args[1];
    if (std.mem.eql(u8, mode, "snapshot") and args.len == 5) return sampleProbe(io, allocator, config, args[3], args[4]);
    if (std.mem.eql(u8, mode, "camera") and args.len == 4) return cameraProbe(io, allocator, config, args[3]);
    if (std.mem.eql(u8, mode, "outer") and args.len == 4) return outerProbe(io, allocator, config, args[3]);
    if (std.mem.eql(u8, mode, "image") and (args.len == 4 or args.len == 5)) return image(io, allocator, config, args[3], if (args.len == 5) try std.fmt.parseInt(usize, args[4], 10) else 1);
    return error.UsageReferenceModeParameterFileOutput;
}

test "strict config parser and binary record framing" {
    const config = try Config.parse("nx 160\nny 160\neps 0.0025\nMBH 6.2e9 # fixed benchmark\n");
    try std.testing.expectEqual(@as(f64, 0.0025), config.eps);
    try std.testing.expectError(error.UnknownParameter, Config.parse("typo 1"));
    try std.testing.expectError(error.UnsupportedBenchmarkParameter, Config.parse("MBH 1"));
    try std.testing.expectError(error.InvalidBenchmarkParameter, Config.parse("eps -1"));
    try std.testing.expectError(error.NonfiniteParameter, Config.parse("rcam nan"));
    try std.testing.expectError(error.TruncatedQueryRecord, queries(3, "broken", 0));
}

test {
    std.testing.refAllDecls(@This());
    _ = @import("geometry.zig");
    _ = @import("snapshot.zig");
    _ = @import("thermal.zig");
    _ = @import("transfer.zig");
}
