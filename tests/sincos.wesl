// Production sincos (geodesic.wesl) on a batch of binary32 angles.
import package::geodesic::sincos;

@group(0) @binding(0) var<storage,read> angles: array<f32>;
@group(0) @binding(1) var<storage,read_write> values: array<vec2<f32>>;

@compute @workgroup_size(64)
fn evaluate(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x >= arrayLength(&angles) { return; }
    values[id.x] = sincos(angles[id.x]);
}
