// Geodesic ray-tracer: null geodesics in Kerr spacetime.
// The Kerr spin axis is +Y, matching the accretion disk normal.

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
    jitter_x:     f32,
    jitter_y:     f32,
    _pad5:        f32,
    _pad6:        f32,
    _pad7:        f32,
}
@group(0) @binding(1) var<uniform> cam: Camera;

struct Disk {
    r1:        f32,
    r2:        f32,
    num:       f32,
    thickness: f32,
    spin:      f32,
    horizon_r: f32,
    isco_r:    f32,
    _pad0:     f32,
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

@group(0) @binding(4) var skybox: texture_2d<f32>;

// -- Constants ---------------------------------------------------------------

const PI:             f32 = 3.141592653589793;
const SAGA_RS:        f32 = 1.269e10;
const BH_M:           f32 = 0.5 * SAGA_RS;
const D_LAMBDA_BASE:  f32 = 1.0e7;
const D_LAMBDA_MAX:   f32 = 1.0e10;
const ESCAPE_R:       f32 = 1.0e13;
const SIN2_FLOOR:     f32 = 1.0e-6;
const DELTA_FLOOR:    f32 = 1.0e-5;

// -- Kerr metric helpers -----------------------------------------------------

fn spin_clamped() -> f32 {
    return clamp(disk.spin, -0.999, 0.999);
}

fn metric_rho(r: f32) -> f32 {
    let horizon_rho = max(disk.horizon_r / BH_M, 1.0);
    return max(r / BH_M, horizon_rho + 1.0e-4);
}

fn safe_sin2(theta: f32) -> f32 {
    let s = sin(theta);
    return max(s * s, SIN2_FLOOR);
}

fn kerr_sigma_hat(rho: f32, theta: f32) -> f32 {
    let a = spin_clamped();
    let c = cos(theta);
    return rho * rho + a * a * c * c;
}

fn kerr_delta_hat(rho: f32) -> f32 {
    let a = spin_clamped();
    return max(rho * rho - 2.0 * rho + a * a, DELTA_FLOOR);
}

fn kerr_big_a_hat(rho: f32, theta: f32) -> f32 {
    let a = spin_clamped();
    let rr_aa = rho * rho + a * a;
    return rr_aa * rr_aa - a * a * kerr_delta_hat(rho) * safe_sin2(theta);
}

fn kerr_lapse(r: f32, theta: f32) -> f32 {
    let rho = metric_rho(r);
    let sigma = kerr_sigma_hat(rho, theta);
    let delta = kerr_delta_hat(rho);
    let big_a = kerr_big_a_hat(rho, theta);
    return sqrt(max(sigma * delta / max(big_a, 1.0e-6), 0.0));
}

fn frame_drag_omega(r: f32, theta: f32) -> f32 {
    let rho = metric_rho(r);
    let a = spin_clamped();
    let big_a = kerr_big_a_hat(rho, theta);
    return 2.0 * a * rho / max(BH_M * big_a, 1.0e-6);
}

fn kerr_static_limit(theta: f32) -> f32 {
    let a = spin_clamped();
    let c = cos(theta);
    return BH_M * (1.0 + sqrt(max(1.0 - a * a * c * c, 0.0)));
}

struct CovMetric {
    g_tt:         f32,
    g_tphi:      f32,
    g_rr:        f32,
    g_thetatheta: f32,
    g_phiphi:    f32,
}

fn cov_metric(r: f32, theta: f32) -> CovMetric {
    let rho = metric_rho(r);
    let a = spin_clamped();
    let sin2_t = safe_sin2(theta);
    let sigma = kerr_sigma_hat(rho, theta);
    let delta = kerr_delta_hat(rho);
    let big_a = kerr_big_a_hat(rho, theta);
    let m2 = BH_M * BH_M;

    var g: CovMetric;
    g.g_tt = -(1.0 - 2.0 * rho / sigma);
    g.g_tphi = -2.0 * a * rho * BH_M * sin2_t / sigma;
    g.g_rr = sigma / delta;
    g.g_thetatheta = m2 * sigma;
    g.g_phiphi = m2 * big_a * sin2_t / sigma;
    return g;
}

struct ContraMetric {
    g_tt:              f32,
    g_tphi:           f32,
    g_rr:             f32,
    g_thetatheta:     f32,
    g_phiphi:         f32,
    dg_tt_dr:         f32,
    dg_tphi_dr:      f32,
    dg_rr_dr:         f32,
    dg_thetatheta_dr: f32,
    dg_phiphi_dr:     f32,
    dg_tt_dt:         f32,
    dg_tphi_dt:      f32,
    dg_rr_dt:         f32,
    dg_thetatheta_dt: f32,
    dg_phiphi_dt:     f32,
}

fn contra_metric(r: f32, theta: f32) -> ContraMetric {
    let rho = metric_rho(r);
    let a = spin_clamped();
    let a2 = a * a;
    let sin_t = sin(theta);
    let cos_t = cos(theta);
    let sin2_raw = sin_t * sin_t;
    let sin2_t = max(sin2_raw, SIN2_FLOOR);
    let d_sin2_dt = select(0.0, 2.0 * sin_t * cos_t, sin2_raw >= SIN2_FLOOR);

    let sigma = rho * rho + a2 * cos_t * cos_t;
    let d_sigma_drho = 2.0 * rho;
    let d_sigma_dt = -2.0 * a2 * sin_t * cos_t;

    let delta_raw = rho * rho - 2.0 * rho + a2;
    let delta = max(delta_raw, DELTA_FLOOR);
    let d_delta_drho = select(0.0, 2.0 * rho - 2.0, delta_raw >= DELTA_FLOOR);

    let rr_aa = rho * rho + a2;
    let big_a = rr_aa * rr_aa - a2 * delta * sin2_t;
    let d_big_a_drho = 4.0 * rho * rr_aa - a2 * d_delta_drho * sin2_t;
    let d_big_a_dt = -a2 * delta * d_sin2_dt;

    let den = max(delta * sigma, 1.0e-6);
    let d_den_drho = d_delta_drho * sigma + delta * d_sigma_drho;
    let d_den_dt = delta * d_sigma_dt;
    let den2 = den * den;

    let inv_m = 1.0 / BH_M;
    let inv_m2 = inv_m * inv_m;

    var g: ContraMetric;
    g.g_tt = -big_a / den;
    g.g_tphi = -2.0 * a * rho * inv_m / den;
    g.g_rr = delta / sigma;
    g.g_thetatheta = inv_m2 / sigma;
    g.g_phiphi = (delta - a2 * sin2_t) * inv_m2 / (den * sin2_t);

    let dgtt_drho = -(d_big_a_drho * den - big_a * d_den_drho) / den2;
    let dgtt_dt = -(d_big_a_dt * den - big_a * d_den_dt) / den2;

    let tphi_num = -2.0 * a * rho;
    let dtphi_num_drho = -2.0 * a;
    let dgtphi_drho = inv_m * (dtphi_num_drho * den - tphi_num * d_den_drho) / den2;
    let dgtphi_dt = -inv_m * tphi_num * d_den_dt / den2;

    let dgrr_drho = (d_delta_drho * sigma - delta * d_sigma_drho) / (sigma * sigma);
    let dgrr_dt = -delta * d_sigma_dt / (sigma * sigma);

    let dgth_drho = -inv_m2 * d_sigma_drho / (sigma * sigma);
    let dgth_dt = -inv_m2 * d_sigma_dt / (sigma * sigma);

    let p = delta - a2 * sin2_t;
    let dp_drho = d_delta_drho;
    let dp_dt = -a2 * d_sin2_dt;
    let pp_den = max(den * sin2_t, 1.0e-6);
    let pp_den2 = pp_den * pp_den;
    let d_pp_den_drho = d_den_drho * sin2_t;
    let d_pp_den_dt = d_den_dt * sin2_t + den * d_sin2_dt;
    let dgpp_drho = inv_m2 * (dp_drho * pp_den - p * d_pp_den_drho) / pp_den2;
    let dgpp_dt = inv_m2 * (dp_dt * pp_den - p * d_pp_den_dt) / pp_den2;

    g.dg_tt_dr = dgtt_drho * inv_m;
    g.dg_tphi_dr = dgtphi_drho * inv_m;
    g.dg_rr_dr = dgrr_drho * inv_m;
    g.dg_thetatheta_dr = dgth_drho * inv_m;
    g.dg_phiphi_dr = dgpp_drho * inv_m;
    g.dg_tt_dt = dgtt_dt;
    g.dg_tphi_dt = dgtphi_dt;
    g.dg_rr_dt = dgrr_dt;
    g.dg_thetatheta_dt = dgth_dt;
    g.dg_phiphi_dt = dgpp_dt;
    return g;
}

// -- Ray state ---------------------------------------------------------------

struct Ray {
    x: f32, y: f32, z: f32,
    r: f32, theta: f32, phi: f32,
    pr: f32, ptheta: f32,
    e: f32, l: f32,
}

fn init_ray(pos: vec3<f32>, dir: vec3<f32>) -> Ray {
    var ray: Ray;
    ray.x = pos.x; ray.y = pos.y; ray.z = pos.z;
    ray.r = max(length(pos), BH_M);
    ray.theta = acos(clamp(pos.y / ray.r, -1.0, 1.0));
    ray.phi = atan2(pos.z, pos.x);

    let sin_t = sin(ray.theta);
    let cos_t = cos(ray.theta);
    let sin_p = sin(ray.phi);
    let cos_p = cos(ray.phi);

    let dr = sin_t * cos_p * dir.x
           + cos_t * dir.y
           + sin_t * sin_p * dir.z;
    let dtheta = (cos_t * cos_p * dir.x
               - sin_t * dir.y
               + cos_t * sin_p * dir.z) / ray.r;
    let dphi_denom = ray.r * sin_t;
    let dphi = select(
        (-sin_p * dir.x + cos_p * dir.z) / dphi_denom,
        0.0,
        abs(dphi_denom) < 1.0e-10
    );

    let g = cov_metric(ray.r, ray.theta);
    let spatial = g.g_rr * dr * dr
                + g.g_thetatheta * dtheta * dtheta
                + g.g_phiphi * dphi * dphi;
    let qa = g.g_tt;
    let qb = 2.0 * g.g_tphi * dphi;
    let disc = max(qb * qb - 4.0 * qa * spatial, 0.0);
    let denom = select(2.0 * qa, -1.0e-6, abs(qa) < 5.0e-7);
    let dt_dlambda = (-qb - sqrt(disc)) / denom;

    ray.e = -(g.g_tt * dt_dlambda + g.g_tphi * dphi);
    ray.l = g.g_tphi * dt_dlambda + g.g_phiphi * dphi;
    ray.pr = g.g_rr * dr;
    ray.ptheta = g.g_thetatheta * dtheta;
    return ray;
}

// -- Geodesic RHS and integration -------------------------------------------

struct Derivs {
    dq: vec3<f32>,
    dp: vec2<f32>,
}

fn geodesic_rhs(ray: Ray) -> Derivs {
    let g = contra_metric(ray.r, ray.theta);
    let e = ray.e;
    let l = ray.l;
    let pr = ray.pr;
    let ptheta = ray.ptheta;

    var d: Derivs;
    d.dq.x = g.g_rr * pr;
    d.dq.y = g.g_thetatheta * ptheta;
    d.dq.z = -g.g_tphi * e + g.g_phiphi * l;

    d.dp.x = -0.5 * (
        g.dg_tt_dr * e * e
        - 2.0 * g.dg_tphi_dr * e * l
        + g.dg_rr_dr * pr * pr
        + g.dg_thetatheta_dr * ptheta * ptheta
        + g.dg_phiphi_dr * l * l
    );
    d.dp.y = -0.5 * (
        g.dg_tt_dt * e * e
        - 2.0 * g.dg_tphi_dt * e * l
        + g.dg_rr_dt * pr * pr
        + g.dg_thetatheta_dt * ptheta * ptheta
        + g.dg_phiphi_dt * l * l
    );
    return d;
}

fn rk4_state(base: Ray, k: Derivs, h: f32) -> Ray {
    var s = base;
    s.r      = base.r      + h * k.dq.x;
    s.theta  = base.theta  + h * k.dq.y;
    s.phi    = base.phi    + h * k.dq.z;
    s.pr     = base.pr     + h * k.dp.x;
    s.ptheta = base.ptheta + h * k.dp.y;
    return s;
}

fn normalize_angles(ray: Ray) -> Ray {
    var r = ray;
    if r.theta < 0.0 {
        r.theta = -r.theta;
        r.phi += PI;
        r.ptheta = -r.ptheta;
    }
    if r.theta > PI {
        r.theta = 2.0 * PI - r.theta;
        r.phi += PI;
        r.ptheta = -r.ptheta;
    }
    return r;
}

fn step_ray(ray: Ray, dL: f32) -> Ray {
    let k1 = geodesic_rhs(ray);
    let k2 = geodesic_rhs(rk4_state(ray, k1, 0.5 * dL));
    let k3 = geodesic_rhs(rk4_state(ray, k2, 0.5 * dL));
    let k4 = geodesic_rhs(rk4_state(ray, k3,       dL));

    let s = dL / 6.0;
    var r = ray;
    r.r      += s * (k1.dq.x + 2.0 * k2.dq.x + 2.0 * k3.dq.x + k4.dq.x);
    r.theta  += s * (k1.dq.y + 2.0 * k2.dq.y + 2.0 * k3.dq.y + k4.dq.y);
    r.phi    += s * (k1.dq.z + 2.0 * k2.dq.z + 2.0 * k3.dq.z + k4.dq.z);
    r.pr     += s * (k1.dp.x + 2.0 * k2.dp.x + 2.0 * k3.dp.x + k4.dp.x);
    r.ptheta += s * (k1.dp.y + 2.0 * k2.dp.y + 2.0 * k3.dp.y + k4.dp.y);
    r = normalize_angles(r);

    let sin_t = sin(r.theta);
    r.x = r.r * sin_t * cos(r.phi);
    r.y = r.r * cos(r.theta);
    r.z = r.r * sin_t * sin(r.phi);
    return r;
}

// -- Intersection tests ------------------------------------------------------

fn crosses_equatorial(old_pos: vec3<f32>, new_pos: vec3<f32>) -> bool {
    let crossed = (old_pos.y * new_pos.y) < 0.0;
    let r_xz = length(vec2<f32>(new_pos.x, new_pos.z));
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
            result.hit = true;
            result.color = objects.color[i];
            result.center = center;
            result.radius = radius;
            return result;
        }
    }
    return result;
}

// -- Disk shading ------------------------------------------------------------

// Novikov-Thorne temperature profile: zero at ISCO, peaks near 1.36 r_isco,
// and falls as r^(-3/4) outward. Returns an unnormalised value; peak is ~0.488.
fn nt_temp(r_disk: f32) -> f32 {
    let f = max(1.0 - sqrt(disk.isco_r / r_disk), 0.0);
    return pow(disk.isco_r / r_disk, 0.75) * pow(f, 0.25);
}

fn blackbody_color(t: f32) -> vec3<f32> {
    let s = clamp(t, 0.0, 1.0);
    if s < 0.4 {
        return mix(vec3<f32>(0.05, 0.0, 0.0), vec3<f32>(1.0, 0.35, 0.02), s / 0.4);
    } else if s < 0.75 {
        return mix(vec3<f32>(1.0, 0.35, 0.02), vec3<f32>(1.0, 0.95, 0.80), (s - 0.4) / 0.35);
    } else {
        return mix(vec3<f32>(1.0, 0.95, 0.80), vec3<f32>(0.65, 0.80, 1.0), (s - 0.75) / 0.25);
    }
}

fn ray_cart_dir(ray: Ray) -> vec3<f32> {
    let g = contra_metric(ray.r, ray.theta);
    let dr = g.g_rr * ray.pr;
    let dtheta = g.g_thetatheta * ray.ptheta;
    let dphi = -g.g_tphi * ray.e + g.g_phiphi * ray.l;

    let sin_t = sin(ray.theta); let cos_t = cos(ray.theta);
    let sin_p = sin(ray.phi);   let cos_p = cos(ray.phi);
    let v = vec3<f32>(
        sin_t * cos_p * dr + ray.r * (cos_t * cos_p * dtheta - sin_t * sin_p * dphi),
        cos_t * dr - ray.r * sin_t * dtheta,
        sin_t * sin_p * dr + ray.r * (cos_t * sin_p * dtheta + sin_t * cos_p * dphi)
    );
    if length(v) < 1.0e-10 {
        return vec3<f32>(1.0, 0.0, 0.0);
    }
    return normalize(v);
}

fn orbital_beta_kerr(r_disk: f32) -> f32 {
    let spin = spin_clamped();
    let orbit_sign = select(-1.0, 1.0, spin >= 0.0);
    let rho = max(r_disk / BH_M, 1.0);
    let omega_orbit = orbit_sign / (BH_M * max(rho * sqrt(rho) + orbit_sign * abs(spin), 1.0e-4));
    let omega_drag = frame_drag_omega(r_disk, 0.5 * PI);
    let lapse = max(kerr_lapse(r_disk, 0.5 * PI), 1.0e-4);

    let sigma = kerr_sigma_hat(metric_rho(r_disk), 0.5 * PI);
    let g_phiphi = (BH_M * BH_M) * kerr_big_a_hat(metric_rho(r_disk), 0.5 * PI) / sigma;
    return clamp(abs((omega_orbit - omega_drag) * sqrt(max(g_phiphi, 0.0)) / lapse), 0.0, 0.95);
}

fn shade_disk(ray: Ray) -> vec4<f32> {
    let disk_pt = vec3<f32>(ray.x, 0.0, ray.z);
    let r_disk = length(disk_pt);

    let base = blackbody_color(nt_temp(r_disk) / 0.488);
    let beta = orbital_beta_kerr(r_disk);
    let spin_dir = select(-1.0, 1.0, spin_clamped() >= 0.0);
    let orbital = spin_dir * normalize(vec3<f32>(-ray.z, 0.0, ray.x));

    let to_cam = -ray_cart_dir(ray);
    let cos_alpha = dot(orbital, to_cam);

    let gamma = 1.0 / sqrt(max(1.0 - beta * beta, 1.0e-6));
    let doppler_kin = 1.0 / max(gamma * (1.0 - beta * cos_alpha), 1.0e-4);
    let d_grav = kerr_lapse(r_disk, 0.5 * PI);
    let doppler = doppler_kin * d_grav;

    let bright = pow(clamp(doppler, 0.05, 8.0), 3.0);
    let shift = clamp((doppler - 1.0) * 2.0, -1.0, 1.0);
    let disk_c = clamp(
        base + vec3<f32>(-shift * 0.35, -shift * 0.1, shift * 0.55),
        vec3<f32>(0.0), vec3<f32>(1.0)
    ) * bright;

    return vec4<f32>(disk_c, r_disk / disk.r2);
}

// -- Skybox ------------------------------------------------------------------

// Equirectangular HDR sample with manual bilinear (texture is Rgba32Float
// and we can't rely on float32-filterable). Reinhard-tonemapped to [0, 1].
fn sample_skybox(dir: vec3<f32>) -> vec3<f32> {
    let dims_u = textureDimensions(skybox);
    let w = i32(dims_u.x);
    let h = i32(dims_u.y);
    let dims = vec2<f32>(f32(w), f32(h));

    let d = normalize(dir);
    let u = atan2(d.z, d.x) * (1.0 / (2.0 * PI)) + 0.5;
    let v = acos(clamp(d.y, -1.0, 1.0)) * (1.0 / PI);

    let px = u * dims.x - 0.5;
    let py = v * dims.y - 0.5;

    let x0_raw = i32(floor(px));
    let y0 = clamp(i32(floor(py)), 0, h - 1);
    let x1_raw = x0_raw + 1;
    let y1 = clamp(y0 + 1, 0, h - 1);
    let fx = px - floor(px);
    let fy = py - floor(py);

    let x0 = ((x0_raw % w) + w) % w;
    let x1 = ((x1_raw % w) + w) % w;

    let c00 = textureLoad(skybox, vec2<i32>(x0, y0), 0).rgb;
    let c10 = textureLoad(skybox, vec2<i32>(x1, y0), 0).rgb;
    let c01 = textureLoad(skybox, vec2<i32>(x0, y1), 0).rgb;
    let c11 = textureLoad(skybox, vec2<i32>(x1, y1), 0).rgb;
    let hdr = mix(mix(c00, c10, fx), mix(c01, c11, fx), fy);

    // Reinhard tonemap so bright nebulae/stars don't clip.
    return hdr / (hdr + vec3<f32>(1.0));
}

// -- Main --------------------------------------------------------------------

@compute @workgroup_size(16, 16, 1)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let dims = textureDimensions(out_image);
    let pix = vec2<i32>(i32(gid.x), i32(gid.y));
    if pix.x >= i32(dims.x) || pix.y >= i32(dims.y) { return; }

    let u = (2.0 * (f32(pix.x) + 0.5 + cam.jitter_x) / f32(dims.x) - 1.0) * cam.aspect * cam.tan_half_fov;
    let v = (1.0 - 2.0 * (f32(pix.y) + 0.5 + cam.jitter_y) / f32(dims.y)) * cam.tan_half_fov;
    let dir = normalize(u * cam.right - v * cam.up + cam.forward);

    var ray = init_ray(cam.pos, dir);
    var prev_pos = vec3<f32>(ray.x, ray.y, ray.z);
    var color = vec4<f32>(0.0);

    var disk_rgb = vec3<f32>(0.0);
    var disk_alpha = 0.0;
    var disk_weight = 1.0;
    var any_disk = false;

    var hit_black_hole = false;
    var hit_object = false;
    var obj_hit: ObjectHit;
    var passed_ergosphere = false;
    var ergosphere_alpha = 0.0;

    for (var i = 0; i < 10000; i++) {
        if ray.r <= disk.horizon_r {
            hit_black_hole = true;
            break;
        }

        let static_limit = kerr_static_limit(ray.theta);
        if ray.r < static_limit {
            passed_ergosphere = true;
            ergosphere_alpha = max(
                ergosphere_alpha,
                clamp((static_limit - ray.r) / max(static_limit - disk.horizon_r, 1.0), 0.0, 1.0)
            );
        }

        let dL = clamp(
            D_LAMBDA_BASE * (ray.r - disk.horizon_r) / SAGA_RS,
            D_LAMBDA_BASE * 0.25,
            D_LAMBDA_MAX
        );
        ray = step_ray(ray, dL);

        let new_pos = vec3<f32>(ray.x, ray.y, ray.z);

        if crosses_equatorial(prev_pos, new_pos) {
            let c = shade_disk(ray);
            disk_rgb += c.rgb * disk_weight;
            disk_alpha = max(disk_alpha, c.a * disk_weight);
            disk_weight *= 0.5;
            any_disk = true;
            if disk_weight < 0.05 { break; }
        }

        obj_hit = intersect_objects(new_pos);
        if obj_hit.hit { hit_object = true; break; }

        prev_pos = new_pos;
        if ray.r > ESCAPE_R { break; }
    }

    if hit_black_hole {
        color = vec4<f32>(0.0, 0.0, 0.0, 1.0);
    } else if hit_object {
        let p = vec3<f32>(ray.x, ray.y, ray.z);
        let n = normalize(p - obj_hit.center);
        let view = normalize(cam.pos - p);
        let diff = max(dot(n, view), 0.0);
        let intensity = 0.1 + 0.9 * diff;
        color = vec4<f32>(obj_hit.color.rgb * intensity, obj_hit.color.a);
    } else {
        var rgb = sample_skybox(ray_cart_dir(ray));
        if passed_ergosphere {
            rgb = mix(rgb, vec3<f32>(0.95, 0.42, 0.08), 0.18 * ergosphere_alpha);
        }
        if any_disk {
            rgb = mix(rgb, disk_rgb, disk_alpha);
        }
        color = vec4<f32>(rgb, 1.0);
    }

    textureStore(out_image, pix, color);
}
