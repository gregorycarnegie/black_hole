import package::thermal::thermal_coefficients;
@group(2) @binding(1) var<storage,read> cases: array<vec4<f32>>;
@group(2) @binding(2) var<storage,read_write> results: array<vec4<f32>>;

@compute @workgroup_size(64)
fn check_thermal(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x*2u >= arrayLength(&cases) { return; }
    let result = thermal_coefficients(cases[id.x*2u].xyz,cases[id.x*2u+1u].x,cases[id.x*2u+1u].y);
    results[id.x*3u]=result.coefficients.emission;
    results[id.x*3u+1u]=result.coefficients.absorption;
    results[id.x*3u+2u]=vec4<f32>(result.coefficients.faraday,select(0.0,1.0,result.valid));
}
