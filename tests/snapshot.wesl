import package::snapshot::sample_snapshot;

@group(1) @binding(4) var<storage,read> positions: array<vec4<f32>>;
@group(1) @binding(5) var<storage,read_write> samples: array<vec4<f32>>;

@compute @workgroup_size(64)
fn check_snapshot(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x >= arrayLength(&positions) { return; }
    let result = sample_snapshot(positions[id.x].xyz);
    samples[4u*id.x] = result.velocity;
    samples[4u*id.x+1u] = result.magnetic;
    samples[4u*id.x+2u] = result.physical;
    samples[4u*id.x+3u] = vec4<f32>(result.native,select(-1.0,select(0.0,1.0,result.emitting),result.valid));
}
