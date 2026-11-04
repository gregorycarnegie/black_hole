// Constant-cell dS/ds = j - K*S, including polarized absorption and Faraday terms.
struct TransferCoefficients {
    emission: vec4<f32>,
    absorption: vec4<f32>,
    faraday: vec3<f32>,
}
struct TransferResult { stokes: vec4<f32>, transmission: mat4x4<f32>, valid: bool }

fn transfer_cell(initial: vec4<f32>, c: TransferCoefficients, ds: f32) -> TransferResult {
    var result: TransferResult;
    if !(ds>=0.0 && ds<1.0e10) || !all(abs(initial)<vec4<f32>(1.0e10)) ||
        !all(abs(c.emission)<vec4<f32>(1.0e10)) || !all(abs(c.absorption)<vec4<f32>(1.0e10)) ||
        !all(abs(c.faraday)<vec3<f32>(1.0e10)) { return result; }
    if c.absorption.x < length(c.absorption.yzw) { return result; }
    let a = c.absorption; let r = c.faraday;
    let k = mat4x4<f32>(vec4<f32>(a.x,a.yzw),vec4<f32>(a.y,a.x,-r.z,r.y),
                       vec4<f32>(a.z,r.z,a.x,-r.x),vec4<f32>(a.w,-r.y,r.x,a.x));
    let identity = mat4x4<f32>(vec4<f32>(1,0,0,0),vec4<f32>(0,1,0,0),
                             vec4<f32>(0,0,1,0),vec4<f32>(0,0,0,1));
    let bound = abs(a.x)+dot(abs(a.yzw)+abs(r),vec3<f32>(1.0));
    var h = ds; var squares = 0u;
    // shortcut: local scaled matrix norm <=8192; subdivide larger cells before calling.
    while bound*h > 0.125 && squares<16u { h*=0.5; squares++; }
    if bound*h > 0.125 { return result; }
    let m = -h*k;
    var exponential = identity; var term = identity; var source = h*c.emission;
    for (var i=1u; i<=12u; i++) {
        term = (1.0/f32(i))*(m*term);
        exponential += term;
        source += (h/f32(i+1u))*(term*c.emission);
    }
    for (var i=0u; i<squares; i++) {
        source = exponential*source+source;
        exponential = exponential*exponential;
    }
    result.stokes = exponential*initial+source;
    result.transmission = exponential;
    result.valid = all(abs(result.stokes)<vec4<f32>(1.0e20));
    return result;
}
