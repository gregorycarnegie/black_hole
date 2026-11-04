// Fast-light iharm MKS sampling; world spin is +Y, and distances are in GM/c².
// The benchmark exporter validates the pinned input and supplies ghost cells.
struct SnapshotHeader {
    start: vec4<f32>,
    spacing: vec4<f32>,
    grid: vec4<f32>,
    geometry: vec4<f32>, // spin, hslope, emission r_min, r_max
    physical: vec4<f32>, // length unit (cm), sigma cut, polar cut, reserved
}
@group(1) @binding(0) var<uniform> snapshot_header: SnapshotHeader;
@group(1) @binding(1) var<storage,read> snapshot_primitives0: array<vec4<f32>>;
@group(1) @binding(2) var<storage,read> snapshot_primitives1: array<vec4<f32>>;
@group(1) @binding(3) var<storage,read> snapshot_physical: array<vec4<f32>>;

struct SnapshotSample {
    velocity: vec4<f32>,
    magnetic: vec4<f32>,
    physical: vec4<f32>, // ne (cm^-3), Theta_e, |B| (G), sigma
    native: vec3<f32>,
    emitting: bool,
    valid: bool,
}

fn snapshot_theta(x2: f32) -> f32 {
    return 3.141592653589793*x2 + 0.5*(1.0-snapshot_header.geometry.y)*sin(6.283185307179586*x2);
}

fn snapshot_index(ijk: vec3<u32>) -> u32 {
    let size = vec3<u32>(snapshot_header.grid.xyz) + vec3<u32>(2u);
    return (ijk.x*size.y + ijk.y)*size.z + ijk.z;
}

fn snapshot_to_world_vector(v: vec4<f32>, r: f32, th: f32, phi: f32, dth: f32) -> vec4<f32> {
    let a = snapshot_header.geometry.x;
    let s = sin(th); let c = cos(th); let cp = cos(phi); let sp = sin(phi);
    let dr = vec3<f32>(r*cp*s, r*c, -r*sp*s);
    let dt = dth*vec3<f32>((r*cp-a*sp)*c, -r*s, -(r*sp+a*cp)*c);
    let dp = vec3<f32>(-(r*sp+a*cp)*s, 0.0, -(r*cp-a*sp)*s);
    return vec4<f32>(v.x, dr*v.y + dt*v.z + dp*v.w);
}

fn sample_snapshot(pos: vec3<f32>) -> SnapshotSample {
    var result: SnapshotSample;
    // Reject nonfinite/outlying queries before coordinate conversion or indexing.
    if !all(abs(pos) <= vec3<f32>(2000.0)) { return result; }
    if all(pos.xz == vec2<f32>(0.0)) { return result; }
    let a = snapshot_header.geometry.x;
    let q = dot(pos,pos)-a*a;
    let root = sqrt(q*q + 4.0*a*a*pos.y*pos.y);
    var r2 = 0.5*(q+root);
    if q < 0.0 { r2 = 2.0*a*a*pos.y*pos.y/max(root-q,1.0e-20); }
    if r2 <= 0.0 { return result; }
    let r = sqrt(r2);
    // atan2 keeps angular resolution near the poles where acos loses it.
    let th = atan2(sqrt(dot(pos.xz,pos.xz)/(r2+a*a)),pos.y/r);
    var lo = 0.0; var hi = 1.0;
    for (var i=0u; i<25u; i++) {
        let mid = 0.5*(lo+hi);
        if snapshot_theta(mid) < th { lo=mid; } else { hi=mid; }
    }
    var phi = atan2(-r*pos.z-a*pos.x,r*pos.x-a*pos.z);
    if phi < 0.0 { phi += 6.283185307179586; }
    let x = vec3<f32>(log(r),0.5*(lo+hi),phi);
    let stop = snapshot_header.start.xyz + snapshot_header.grid.xyz*snapshot_header.spacing.xyz;
    if any(x.xy < snapshot_header.start.xy) || any(x.xy >= stop.xy) { return result; }
    let base = clamp(floor((x-snapshot_header.start.xyz)/snapshot_header.spacing.xyz-0.5),vec3<f32>(-1.0),snapshot_header.grid.xyz-1.0);
    let d = clamp((x-(snapshot_header.start.xyz+(base+0.5)*snapshot_header.spacing.xyz))/snapshot_header.spacing.xyz,vec3<f32>(0.0),vec3<f32>(1.0));
    let ijk = vec3<u32>(base+1.0);
    var p0 = vec4<f32>(0.0); var p1 = vec4<f32>(0.0); var physical = vec4<f32>(0.0);
    for (var k=0u; k<2u; k++) {
        for (var j=0u; j<2u; j++) {
            for (var i=0u; i<2u; i++) {
                let w = select(1.0-d.x,d.x,i==1u)*select(1.0-d.y,d.y,j==1u)*select(1.0-d.z,d.z,k==1u);
                let index = snapshot_index(ijk+vec3<u32>(i,j,k));
                p0 += w*snapshot_primitives0[index]; p1 += w*snapshot_primitives1[index];
                physical += w*snapshot_physical[index];
            }
        }
    }
    let s2 = sin(th)*sin(th); let rho2 = r2+a*a*cos(th)*cos(th); let f = 2.0*r/rho2;
    let dth = 3.141592653589793*(1.0+(1.0-snapshot_header.geometry.y)*cos(6.283185307179586*x.y));
    let g = mat4x4<f32>(
        vec4<f32>(-1.0+f,f*r,0.0,-a*f*s2),
        vec4<f32>(f*r,(1.0+f)*r2,0.0,-a*s2*(1.0+f)*r),
        vec4<f32>(0.0,0.0,rho2*dth*dth,0.0),
        vec4<f32>(-a*f*s2,-a*s2*(1.0+f)*r,0.0,s2*(rho2+a*a*s2*(1.0+f))));
    let v = vec4<f32>(0.0,p0.zw,p1.x);
    let fac = sqrt((1.0+abs(dot(v,g*v)))/(1.0+f));
    let u = vec4<f32>(fac*(1.0+f),v.y-fac*f/r,v.zw);
    let b0 = dot(p1.yzw,(g*u).yzw);
    let b = vec4<f32>(b0,(p1.yzw+u.yzw*b0)/u.x);
    result.velocity = snapshot_to_world_vector(u,r,th,phi,dth);
    result.magnetic = snapshot_to_world_vector(b,r,th,phi,dth);
    physical.x = select(0.0,physical.x,physical.w<snapshot_header.physical.y);
    result.physical = physical;
    result.native = x;
    result.emitting = r>snapshot_header.geometry.z && r<snapshot_header.geometry.w && th>snapshot_header.physical.z && th<3.141592653589793-snapshot_header.physical.z;
    result.valid = true;
    return result;
}
