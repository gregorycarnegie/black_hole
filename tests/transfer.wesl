import package::polarized_transfer::{TransferCoefficients, transfer_cell};
@group(0) @binding(0) var<storage,read> cases: array<vec4<f32>>;
@group(0) @binding(1) var<storage,read_write> results: array<vec4<f32>>;

@compute @workgroup_size(64)
fn check_transfer(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x*4u >= arrayLength(&cases) { return; }
    var c: TransferCoefficients;
    c.emission=cases[id.x*4u]; c.absorption=cases[id.x*4u+1u]; c.faraday=cases[id.x*4u+2u].xyz;
    let result=transfer_cell(cases[id.x*4u+3u],c,cases[id.x*4u+2u].w);
    results[id.x*2u]=result.stokes;
    results[id.x*2u+1u]=vec4<f32>(select(0.0,1.0,result.valid),0.0,0.0,0.0);
}
