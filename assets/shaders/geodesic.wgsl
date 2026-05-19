// Geodesic ray-tracer: null geodesics in Schwarzschild spacetime.
// Ported from geodesic.comp (GLSL compute shader).

@group(0) @binding(0) var out_image: texture_storage_2d<rgba8unorm, write>;

struct Camera {
    pos:          vec3<f32>,
    _pad0:        f32,
    right:        vec3<f32>,
    _pad1:        f32,
    up:           vec3<f32>,
    _pad2:        f32,
    forward:      vec3<f32>,
    _pad3:        f32,
    tan_half_fov: f32,
    aspect:       f32,
    moving:       u32,
    _pad4:        u32,
}
@group(0) @binding(1) var<uniform> cam: Camera;

struct Disk {
    r1:        f32,
    r2:        f32,
    num:       f32,
    thickness: f32,
}
@group(0) @binding(2) var<uniform> disk: Disk;

struct Objects {
    num_objects: i32,
    _pad0:       f32,
    _pad1:       f32,
    _pad2:       f32,
    pos_radius:  array<vec4<f32>, 16>,
    color:       array<vec4<f32>, 16>,
    // std140 pads f32 array elements to 16 bytes; only .x is used
    mass:        array<vec4<f32>, 16>,
}
@group(0) @binding(3) var<uniform> objects: Objects;

// ── Constants ────────────────────────────────────────────────────────────────

const SAGA_RS:        f32 = 1.269e10;
const D_LAMBDA_BASE:  f32 = 1.0e7;   // step size at r == r_s
const D_LAMBDA_MAX:   f32 = 1.0e10;  // cap for far-field rays
const ESCAPE_R:       f32 = 1.0e13;  // ~100x camera radius; reachable with adaptive dL

// ── Ray state ────────────────────────────────────────────────────────────────

struct Ray {
    x: f32, y: f32, z: f32,
    r: f32, theta: f32, phi: f32,
    dr: f32, dtheta: f32, dphi: f32,
    e: f32, l: f32,   // conserved energy and angular momentum
}

fn init_ray(pos: vec3<f32>, dir: vec3<f32>) -> Ray {
    var ray: Ray;
    ray.x = pos.x; ray.y = pos.y; ray.z = pos.z;
    ray.r     = length(pos);
    ray.theta = acos(pos.z / ray.r);
    ray.phi   = atan2(pos.y, pos.x);

    let dx = dir.x; let dy = dir.y; let dz = dir.z;
    ray.dr     = sin(ray.theta)*cos(ray.phi)*dx
               + sin(ray.theta)*sin(ray.phi)*dy
               + cos(ray.theta)*dz;
    ray.dtheta = (cos(ray.theta)*cos(ray.phi)*dx
               + cos(ray.theta)*sin(ray.phi)*dy
               - sin(ray.theta)*dz) / ray.r;
    let dphi_denom = ray.r * sin(ray.theta);
    ray.dphi = select(
        (-sin(ray.phi)*dx + cos(ray.phi)*dy) / dphi_denom,
        0.0,
        abs(dphi_denom) < 1e-10
    );

    ray.l = ray.r * ray.r * sin(ray.theta) * ray.dphi;

    let f     = 1.0 - SAGA_RS / ray.r;
    let dt_dL = sqrt(
        (ray.dr * ray.dr) / f
        + ray.r * ray.r * (ray.dtheta * ray.dtheta
            + sin(ray.theta) * sin(ray.theta) * ray.dphi * ray.dphi)
    );
    ray.e = f * dt_dL;

    return ray;
}

// ── Geodesic RHS and integration ─────────────────────────────────────────────

struct Derivs { d1: vec3<f32>, d2: vec3<f32> }

fn geodesic_rhs(ray: Ray) -> Derivs {
    let r     = ray.r;
    let theta = ray.theta;
    let dr    = ray.dr;
    let dtheta = ray.dtheta;
    let dphi   = ray.dphi;
    let f      = 1.0 - SAGA_RS / r;
    let dt_dL  = ray.e / f;

    var d: Derivs;
    d.d1 = vec3<f32>(dr, dtheta, dphi);
    d.d2.x = -(SAGA_RS / (2.0 * r * r)) * f * dt_dL * dt_dL
             + (SAGA_RS / (2.0 * r * r * f)) * dr * dr
             + r * (dtheta * dtheta + sin(theta) * sin(theta) * dphi * dphi);
    d.d2.y = -2.0 * dr * dtheta / r
             + sin(theta) * cos(theta) * dphi * dphi;
    let sin_t  = sin(theta);
    let cot_t  = select(cos(theta) / sin_t, 0.0, abs(sin_t) < 1e-10);
    d.d2.z = -2.0 * dr * dphi / r
             - 2.0 * cot_t * dtheta * dphi;
    return d;
}

fn rk4_state(base: Ray, k: Derivs, h: f32) -> Ray {
    var s    = base;
    s.r      = base.r      + h * k.d1.x;
    s.theta  = base.theta  + h * k.d1.y;
    s.phi    = base.phi    + h * k.d1.z;
    s.dr     = base.dr     + h * k.d2.x;
    s.dtheta = base.dtheta + h * k.d2.y;
    s.dphi   = base.dphi   + h * k.d2.z;
    return s;
}

fn step_ray(ray: Ray, dL: f32) -> Ray {
    let k1 = geodesic_rhs(ray);
    let k2 = geodesic_rhs(rk4_state(ray, k1, 0.5 * dL));
    let k3 = geodesic_rhs(rk4_state(ray, k2, 0.5 * dL));
    let k4 = geodesic_rhs(rk4_state(ray, k3,       dL));

    let s = dL / 6.0;
    var r = ray;
    r.r      += s * (k1.d1.x + 2.0*k2.d1.x + 2.0*k3.d1.x + k4.d1.x);
    r.theta  += s * (k1.d1.y + 2.0*k2.d1.y + 2.0*k3.d1.y + k4.d1.y);
    r.phi    += s * (k1.d1.z + 2.0*k2.d1.z + 2.0*k3.d1.z + k4.d1.z);
    r.dr     += s * (k1.d2.x + 2.0*k2.d2.x + 2.0*k3.d2.x + k4.d2.x);
    r.dtheta += s * (k1.d2.y + 2.0*k2.d2.y + 2.0*k3.d2.y + k4.d2.y);
    r.dphi   += s * (k1.d2.z + 2.0*k2.d2.z + 2.0*k3.d2.z + k4.d2.z);

    r.x = r.r * sin(r.theta) * cos(r.phi);
    r.y = r.r * sin(r.theta) * sin(r.phi);
    r.z = r.r * cos(r.theta);
    return r;
}

// ── Intersection tests ───────────────────────────────────────────────────────

fn crosses_equatorial(old_pos: vec3<f32>, new_pos: vec3<f32>) -> bool {
    let crossed = (old_pos.y * new_pos.y) < 0.0;
    let r_xz    = length(vec2<f32>(new_pos.x, new_pos.z));
    return crossed && (r_xz >= disk.r1) && (r_xz <= disk.r2);
}

struct ObjectHit { hit: bool, color: vec4<f32>, center: vec3<f32>, radius: f32 }

fn intersect_objects(pos: vec3<f32>) -> ObjectHit {
    var result: ObjectHit;
    result.hit = false;
    for (var i = 0; i < objects.num_objects; i++) {
        let center = objects.pos_radius[i].xyz;
        let radius = objects.pos_radius[i].w;
        if distance(pos, center) <= radius {
            result.hit    = true;
            result.color  = objects.color[i];
            result.center = center;
            result.radius = radius;
            return result;
        }
    }
    return result;
}

// ── Main ─────────────────────────────────────────────────────────────────────

@compute @workgroup_size(16, 16, 1)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let dims = textureDimensions(out_image);
    let pix  = vec2<i32>(i32(gid.x), i32(gid.y));
    if pix.x >= i32(dims.x) || pix.y >= i32(dims.y) { return; }

    let u = (2.0 * (f32(pix.x) + 0.5) / f32(dims.x) - 1.0) * cam.aspect * cam.tan_half_fov;
    let v = (1.0 - 2.0 * (f32(pix.y) + 0.5) / f32(dims.y)) * cam.tan_half_fov;
    let dir = normalize(u * cam.right - v * cam.up + cam.forward);

    var ray      = init_ray(cam.pos, dir);
    var prev_pos = vec3<f32>(ray.x, ray.y, ray.z);
    var color    = vec4<f32>(0.0);

    var hit_black_hole = false;
    var hit_disk       = false;
    var hit_object     = false;
    var obj_hit: ObjectHit;

    for (var i = 0; i < 10000; i++) {
        if ray.r <= SAGA_RS { hit_black_hole = true; break; }

        let dL = clamp(D_LAMBDA_BASE * (ray.r / SAGA_RS), D_LAMBDA_BASE, D_LAMBDA_MAX);
        ray = step_ray(ray, dL);

        let new_pos = vec3<f32>(ray.x, ray.y, ray.z);

        if crosses_equatorial(prev_pos, new_pos) { hit_disk = true; break; }

        obj_hit = intersect_objects(new_pos);
        if obj_hit.hit { hit_object = true; break; }

        prev_pos = new_pos;
        if ray.r > ESCAPE_R { break; }
    }

    if hit_disk {
        let r      = length(vec3<f32>(ray.x, ray.y, ray.z)) / disk.r2;
        let disk_c = vec3<f32>(1.0, r, 0.2);
        color      = vec4<f32>(disk_c, r);

    } else if hit_black_hole {
        color = vec4<f32>(0.0, 0.0, 0.0, 1.0);

    } else if hit_object {
        let P         = vec3<f32>(ray.x, ray.y, ray.z);
        let N         = normalize(P - obj_hit.center);
        let V         = normalize(cam.pos - P);
        let diff      = max(dot(N, V), 0.0);
        let intensity = 0.1 + 0.9 * diff;
        color         = vec4<f32>(obj_hit.color.rgb * intensity, obj_hit.color.a);

    } else {
        color = vec4<f32>(0.0);
    }

    textureStore(out_image, pix, color);
}
