// Production atan2_arith (geodesic.wesl) on a batch of binary32 (y, x) pairs.
import package::geodesic::atan2_arith;

@group(0) @binding(0) var<storage,read> points: array<vec2<f32>>;
@group(0) @binding(1) var<storage,read_write> values: array<f32>;

@compute @workgroup_size(64)
fn evaluate(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x >= arrayLength(&points) { return; }
    values[id.x] = atan2_arith(points[id.x].x, points[id.x].y);
}
