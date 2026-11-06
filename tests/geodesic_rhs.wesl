// Production geodesic_rhs (geodesic.wesl) on a batch of exact binary32 inputs,
// laid out as BlackHole.WgslGeodesic reads them: inv 0-15, dx 16-31, dy 32-47,
// dz 48-63 (entry 4 i + j is row i, column j), momentum 64-67, screen 68-71.
import package::geodesic::{geodesic_rhs, Ray, Metric};

@group(0) @binding(0) var<storage,read> inputs: array<f32>;
@group(0) @binding(1) var<storage,read_write> values: array<f32>;

fn matrix(base: u32) -> mat4x4<f32> {
    var m: mat4x4<f32>;
    for (var c = 0u; c < 4u; c++) {
        for (var r = 0u; r < 4u; r++) { m[c][r] = inputs[base + 4u*r + c]; }
    }
    return m;
}

fn vec4_at(base: u32) -> vec4<f32> {
    return vec4<f32>(inputs[base], inputs[base+1u], inputs[base+2u], inputs[base+3u]);
}

@compute @workgroup_size(64)
fn evaluate(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x >= arrayLength(&inputs) / 72u { return; }
    let b = id.x * 72u;
    var m: Metric;
    m.inv = matrix(b); m.dx = matrix(b+16u); m.dy = matrix(b+32u); m.dz = matrix(b+48u);
    let d = geodesic_rhs(Ray(vec3<f32>(0.0), vec4_at(b+64u), vec4_at(b+68u)), m);
    let o = id.x * 11u;
    values[o] = d.pos.x; values[o+1u] = d.pos.y; values[o+2u] = d.pos.z;
    for (var i = 0u; i < 4u; i++) { values[o+3u+i] = d.p[i]; values[o+7u+i] = d.screen[i]; }
}
