// Production adaptive stepping on long single-hole rays (obligation N3).
// Each invocation starts at (impact, 0, 100) heading along -z, builds the
// initial state with init_ray's lapse/shift formulas, and advances with the
// renderer's step-size rule until the affine parameter reaches `span`.
import package::geodesic::{Ray, scene_metric, advance_ray, spatial_metric, spatial_unit, STEP_TOLERANCE};

struct Case { impact: f32, span: f32, _pad0: f32, _pad1: f32 }
@group(1) @binding(0) var<storage,read> cases: array<Case>;
@group(1) @binding(1) var<storage,read_write> results: array<vec4<f32>>;

@compute @workgroup_size(1)
fn trace(@builtin(global_invocation_id) id: vec3<u32>) {
    let c = cases[id.x];
    let pos = vec3<f32>(c.impact,0.0,100.0);
    var metric = scene_metric(pos);
    let gamma = spatial_metric(metric);
    let n = spatial_unit(vec3<f32>(0.0,0.0,-1.0),gamma);
    let lapse = inverseSqrt(-metric.inv[0][0]);
    let shift = -metric.inv[0].yzw/metric.inv[0][0];
    let k = vec4<f32>(-1.0/lapse, n+shift/lapse);
    let right = spatial_unit(vec3<f32>(1.0,0.0,0.0)-n*dot(n,gamma*vec3<f32>(1.0,0.0,0.0)),gamma);
    var ray = Ray(pos,metric.g*k,vec4<f32>(0.0,right));
    let start = ray;
    var affine = 0.0;
    var next_h = 1.0e8;
    var steps = 0u;
    var status = 1.0;
    for (var i=0u; i<200000u && affine<c.span; i++) {
        if metric.clearance < 0.002 || !metric.valid { status = 2.0; break; }
        let velocity = (metric.inv*ray.p).yzw;
        let distance = clamp(0.12*metric.clearance,0.0002,32.0);
        let wanted = min(min(distance/max(length(velocity),1.0e-6),next_h),c.span-affine);
        let step = advance_ray(ray,wanted,metric);
        if !step.accepted { status = 3.0; break; }
        affine += step.h;
        next_h = step.h*clamp(0.9*pow(STEP_TOLERANCE/max(step.error,1.0e-20),0.2),0.5,2.0);
        ray = step.ray;
        metric = scene_metric(ray.pos);
        steps++;
    }
    let base = 4u*id.x;
    results[base] = vec4<f32>(start.pos,status);
    results[base+1u] = start.p;
    results[base+2u] = vec4<f32>(ray.pos,affine);
    results[base+3u] = vec4<f32>(ray.p.yzw,f32(steps));
}
