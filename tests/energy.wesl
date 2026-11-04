// Fluid-frame photon energies seen by the production renderer (obligation P1).
// Each invocation traces one pixel with main()'s stepping rules and records
// the minimum and maximum `sample_plasma(...).energy` over disk samples.
import package::geodesic::{Ray, scene_metric, advance_ray, init_ray, sample_plasma, disk_radius,
    get_h_over_r, disk_midplane_y, screen_frame, cam, disk, STEP_TOLERANCE, ESCAPE_R};

@group(1) @binding(0) var<storage,read_write> extremes: array<vec4<f32>>;

@compute @workgroup_size(8,8)
fn energies(@builtin(global_invocation_id) gid: vec3<u32>) {
    let n = 32u;
    if gid.x >= n || gid.y >= n { return; }
    let u = (2.0*(f32(gid.x)+0.5)/f32(n)-1.0)*cam.aspect*cam.tan_half_fov;
    let v = (1.0-2.0*(f32(gid.y)+0.5)/f32(n))*cam.tan_half_fov;
    let dir = normalize(u*cam.right-v*cam.up+cam.forward);
    var metric = scene_metric(cam.pos);
    var low = 1.0e30; var high = -1.0e30; var samples = 0.0;
    if metric.valid && metric.clearance > 0.0 {
        var ray = init_ray(cam.pos,dir,metric);
        var next_h = 1.0e8;
        for (var i=0u; i<cam.max_iter; i++) {
            if metric.clearance < 0.002 || !metric.valid { break; }
            let velocity = (metric.inv*ray.p).yzw;
            var distance = clamp(0.12*metric.clearance,0.0002,32.0);
            let radius = disk_radius(ray.pos,disk.spin,disk.binary_enabled!=0u);
            let height = max(get_h_over_r(max(radius,disk.r1))*max(radius,disk.r1),0.001);
            if radius > disk.r1-distance && radius < disk.r2+distance {
                let mid = disk_midplane_y(max(radius,0.001),atan2(ray.pos.z,ray.pos.x));
                let to_disk = max(abs(ray.pos.y-mid)-4.0*height,0.0);
                distance = min(distance,max(0.25*height,0.5*to_disk));
            }
            let step = advance_ray(ray,min(distance/max(length(velocity),1.0e-6),next_h),metric);
            if !step.accepted { break; }
            next_h = step.h*clamp(0.9*pow(STEP_TOLERANCE/max(step.error,1.0e-20),0.2),0.5,2.0);
            ray = step.ray;
            metric = scene_metric(ray.pos);
            ray.screen = vec4<f32>(0.0,screen_frame(ray,metric)[0]);
            let plasma = sample_plasma(ray,metric);
            if plasma.alpha > 0.0 {
                low = min(low,plasma.energy); high = max(high,plasma.energy); samples += 1.0;
            }
            if length(ray.pos)>ESCAPE_R { break; }
        }
    }
    extremes[gid.y*n+gid.x] = vec4<f32>(low,high,samples,0.0);
}
