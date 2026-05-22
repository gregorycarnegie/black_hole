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
    tan_half_fov:  f32,
    aspect:        f32,
    moving:        u32,
    jitter_x:      f32,
    jitter_y:      f32,
    debug_heatmap: u32,
    _pad6:         f32,
    _pad7:         f32,
}
@group(0) @binding(1) var<uniform> cam: Camera;

struct Disk {
    r1:        f32,   // inner emitting radius
    r2:        f32,   // outer radius
    h_thin:    f32,   // H/R for thin disk component
    h_hot:     f32,   // H/R for hot / thick inner component
    spin:      f32,
    horizon_r: f32,
    isco_r:    f32,
    r_trunc:   f32,   // truncation radius (TruncHot) or puff radius (Slim)
    tilt_deg:  f32,   // outer disk tilt in degrees (Warped)
    r_bp:      f32,   // Bardeen-Petterson alignment radius (Warped)
    twist_deg: f32,   // azimuthal twist per ln(r/r_bp) in degrees (Warped)
    model:     u32,   // 0=ThinNT  1=TruncHot  2=Slim  3=Warped
    _pad0:     f32,
    _pad1:     f32,
    _pad2:     f32,
    _pad3:     f32,
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
const INV_BH_M:       f32 = 1.0 / BH_M;
const INV_BH_M2:      f32 = INV_BH_M * INV_BH_M;
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
    let horizon_rho = max(disk.horizon_r * INV_BH_M, 1.0);
    return max(r * INV_BH_M, horizon_rho + 1.0e-4);
}

fn kerr_static_limit(theta: f32, a2: f32) -> f32 {
    let c = cos(theta);
    return BH_M * (1.0 + sqrt(max(1.0 - a2 * c * c, 0.0)));
}

struct CovMetric {
    g_tt:         f32,
    g_tphi:      f32,
    g_rr:        f32,
    g_thetatheta: f32,
    g_phiphi:    f32,
}

fn cov_metric(r: f32, theta: f32, a: f32) -> CovMetric {
    let rho = metric_rho(r);
    let a2 = a * a;
    let sin_t = sin(theta);
    let cos_t = cos(theta);
    let sin2_t = max(sin_t * sin_t, SIN2_FLOOR);
    let rho2 = rho * rho;
    let sigma = rho2 + a2 * cos_t * cos_t;
    let delta = max(rho2 - 2.0 * rho + a2, DELTA_FLOOR);
    let rr_aa = rho2 + a2;
    let big_a = rr_aa * rr_aa - a2 * delta * sin2_t;
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

fn contra_metric(r: f32, theta: f32, a: f32) -> ContraMetric {
    let rho = metric_rho(r);
    let rho2 = rho * rho;
    let a2 = a * a;
    let sin_t = sin(theta);
    let cos_t = cos(theta);
    let sin2_raw = sin_t * sin_t;
    let sin2_t = max(sin2_raw, SIN2_FLOOR);
    let d_sin2_dt = select(0.0, 2.0 * sin_t * cos_t, sin2_raw >= SIN2_FLOOR);

    let sigma = rho2 + a2 * cos_t * cos_t;
    let d_sigma_drho = 2.0 * rho;
    let d_sigma_dt = -2.0 * a2 * sin_t * cos_t;

    let delta_raw = rho2 - 2.0 * rho + a2;
    let delta = max(delta_raw, DELTA_FLOOR);
    let d_delta_drho = select(0.0, 2.0 * rho - 2.0, delta_raw >= DELTA_FLOOR);

    let rr_aa = rho2 + a2;
    let big_a = rr_aa * rr_aa - a2 * delta * sin2_t;
    let d_big_a_drho = 4.0 * rho * rr_aa - a2 * d_delta_drho * sin2_t;
    let d_big_a_dt = -a2 * delta * d_sin2_dt;

    let den = max(delta * sigma, 1.0e-6);
    let d_den_drho = d_delta_drho * sigma + delta * d_sigma_drho;
    let d_den_dt = delta * d_sigma_dt;
    let inv_den = 1.0 / den;
    let inv_den2 = inv_den * inv_den;
    let inv_sigma = 1.0 / sigma;
    let inv_sigma2 = inv_sigma * inv_sigma;
    let inv_sin2 = 1.0 / sin2_t;

    var g: ContraMetric;
    let p = delta - a2 * sin2_t;
    g.g_tt = -big_a * inv_den;
    g.g_tphi = -2.0 * a * rho * INV_BH_M * inv_den;
    g.g_rr = delta * inv_sigma;
    g.g_thetatheta = INV_BH_M2 * inv_sigma;
    g.g_phiphi = p * INV_BH_M2 * inv_den * inv_sin2;

    let dgtt_drho = -(d_big_a_drho * den - big_a * d_den_drho) * inv_den2;
    let dgtt_dt = -(d_big_a_dt * den - big_a * d_den_dt) * inv_den2;

    let tphi_num = -2.0 * a * rho;
    let dtphi_num_drho = -2.0 * a;
    let dgtphi_drho = INV_BH_M * (dtphi_num_drho * den - tphi_num * d_den_drho) * inv_den2;
    let dgtphi_dt = -INV_BH_M * tphi_num * d_den_dt * inv_den2;

    let dgrr_drho = (d_delta_drho * sigma - delta * d_sigma_drho) * inv_sigma2;
    let dgrr_dt = -delta * d_sigma_dt * inv_sigma2;

    let dgth_drho = -INV_BH_M2 * d_sigma_drho * inv_sigma2;
    let dgth_dt = -INV_BH_M2 * d_sigma_dt * inv_sigma2;

    let dp_drho = d_delta_drho;
    let dp_dt = -a2 * d_sin2_dt;
    let pp_den = den * sin2_t;
    let inv_pp_den = select(1.0e6, inv_den * inv_sin2, pp_den >= 1.0e-6);
    let inv_pp_den2 = inv_pp_den * inv_pp_den;
    let d_pp_den_drho = d_den_drho * sin2_t;
    let d_pp_den_dt = d_den_dt * sin2_t + den * d_sin2_dt;
    let dgpp_drho = INV_BH_M2 * (dp_drho * pp_den - p * d_pp_den_drho) * inv_pp_den2;
    let dgpp_dt = INV_BH_M2 * (dp_dt * pp_den - p * d_pp_den_dt) * inv_pp_den2;

    g.dg_tt_dr = dgtt_drho * INV_BH_M;
    g.dg_tphi_dr = dgtphi_drho * INV_BH_M;
    g.dg_rr_dr = dgrr_drho * INV_BH_M;
    g.dg_thetatheta_dr = dgth_drho * INV_BH_M;
    g.dg_phiphi_dr = dgpp_drho * INV_BH_M;
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

fn init_ray(pos: vec3<f32>, dir: vec3<f32>, a: f32) -> Ray {
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

    let g = cov_metric(ray.r, ray.theta, a);
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

fn geodesic_rhs(ray: Ray, a: f32) -> Derivs {
    let g = contra_metric(ray.r, ray.theta, a);
    let e = ray.e;
    let l = ray.l;
    let pr = ray.pr;
    let ptheta = ray.ptheta;
    let e2 = e * e;
    let two_el = 2.0 * e * l;
    let pr2 = pr * pr;
    let ptheta2 = ptheta * ptheta;
    let l2 = l * l;

    var d: Derivs;
    d.dq.x = g.g_rr * pr;
    d.dq.y = g.g_thetatheta * ptheta;
    d.dq.z = -g.g_tphi * e + g.g_phiphi * l;

    d.dp.x = -0.5 * (
        g.dg_tt_dr * e2
        - g.dg_tphi_dr * two_el
        + g.dg_rr_dr * pr2
        + g.dg_thetatheta_dr * ptheta2
        + g.dg_phiphi_dr * l2
    );
    d.dp.y = -0.5 * (
        g.dg_tt_dt * e2
        - g.dg_tphi_dt * two_el
        + g.dg_rr_dt * pr2
        + g.dg_thetatheta_dt * ptheta2
        + g.dg_phiphi_dt * l2
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

fn step_ray(ray: Ray, dL: f32, a: f32) -> Ray {
    let k1 = geodesic_rhs(ray, a);
    let k2 = geodesic_rhs(rk4_state(ray, k1, 0.5 * dL), a);
    let k3 = geodesic_rhs(rk4_state(ray, k2, 0.5 * dL), a);
    let k4 = geodesic_rhs(rk4_state(ray, k3,       dL), a);

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

struct ObjectHit { hit: bool, color: vec4<f32>, center: vec3<f32>, radius: f32 }

fn intersect_objects(pos: vec3<f32>) -> ObjectHit {
    var result: ObjectHit;
    result.hit = false;
    for (var i = 0; i < objects.num_objects; i++) {
        let center = objects.pos_radius[i].xyz;
        let radius = objects.pos_radius[i].w;
        let offset = pos - center;
        if radius >= 0.0 && dot(offset, offset) <= radius * radius {
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
    let ratio = disk.isco_r / r_disk;
    let sqrt_ratio = sqrt(ratio);
    let f = max(1.0 - sqrt_ratio, 0.0);
    return sqrt_ratio * sqrt(sqrt_ratio) * sqrt(sqrt(f));
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

fn disk_edge_fade(r_disk: f32) -> f32 {
    let edge_width = max(0.06 * (disk.r2 - disk.r1), 0.35 * SAGA_RS);
    let inner = smoothstep(disk.r1, disk.r1 + edge_width, r_disk);
    let outer = 1.0 - smoothstep(disk.r2 - edge_width, disk.r2, r_disk);
    return clamp(inner * outer, 0.0, 1.0);
}

// Model-dependent H/R at cylindrical radius r_xz.
fn get_h_over_r(r_xz: f32) -> f32 {
    if disk.model == 1u {
        // TruncHot: tanh transition — h_hot inside r_trunc, h_thin outside.
        let safe_r  = max(r_xz,        SAGA_RS * 1.0e-3);
        let safe_rt = max(disk.r_trunc, SAGA_RS * 1.0e-3);
        let t = clamp((log(safe_r) - log(safe_rt)) / 0.4, -10.0, 10.0);
        let w = 0.5 * (1.0 + tanh(t));   // 0 deep inside, 1 far outside
        return w * disk.h_thin + (1.0 - w) * disk.h_hot;
    } else if disk.model == 2u {
        // Slim / super-Eddington: disk puffs up inward at r_trunc (used as r_puff).
        let r_puff = max(disk.r_trunc, SAGA_RS * 0.5);
        let ratio  = r_xz / r_puff;
        return disk.h_thin + (disk.h_hot - disk.h_thin) / (1.0 + ratio * ratio);
    }
    // ThinNT (0) or WarpedThin (3): constant H/R.
    return disk.h_thin;
}

// Midplane Y displacement for a warped disk; zero for all other models.
// β(R): tilt 0 inside r_bp (aligned), tilt_deg outside. γ(R): azimuthal twist.
fn disk_midplane_y(r_xz: f32, phi: f32) -> f32 {
    if disk.model != 3u { return 0.0; }
    let r_bp_safe = max(disk.r_bp, SAGA_RS * 0.1);
    let ln_norm   = clamp(log(max(r_xz, SAGA_RS * 0.01) / r_bp_safe) / 0.5, -10.0, 10.0);
    let w     = 0.5 * (1.0 + tanh(ln_norm));   // 0 inside r_bp, 1 outside
    let beta  = disk.tilt_deg  * (PI / 180.0) * w;
    let gamma = disk.twist_deg * (PI / 180.0) * log(1.0 + r_xz / r_bp_safe);
    return r_xz * sin(beta) * sin(phi - gamma);
}

// Sub-Keplerian factor: 1.0 for razor-thin, ~0.5 for thick hot flow.
fn sub_keplerian_factor(h_r: f32) -> f32 {
    return 1.0 - 0.5 * clamp(h_r * 2.0, 0.0, 1.0);
}

// Normalised emissivity temperature for optically-thin RIAF / hot flow.
fn hot_emissivity_t(r: f32) -> f32 {
    let r0 = max(disk.isco_r, disk.r1);
    return pow(clamp(r0 / max(r, r0), 0.0, 1.0), 0.6);
}

// Blackbody colour for synchrotron-dominated hot flow (orange → pale gold).
fn hot_blackbody_color(t: f32) -> vec3<f32> {
    let s = clamp(t, 0.0, 1.0);
    if s < 0.5 {
        return mix(vec3<f32>(0.02, 0.01, 0.0), vec3<f32>(0.85, 0.30, 0.05), s * 2.0);
    }
    return mix(vec3<f32>(0.85, 0.30, 0.05), vec3<f32>(1.0, 0.80, 0.50), (s - 0.5) * 2.0);
}

fn ray_cart_dir(ray: Ray, a: f32) -> vec3<f32> {
    let g = contra_metric(ray.r, ray.theta, a);
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
    let len2 = dot(v, v);
    if len2 < 1.0e-20 {
        return vec3<f32>(1.0, 0.0, 0.0);
    }
    return v * inverseSqrt(len2);
}

struct OrbitalResult {
    beta:       f32,
    lapse:      f32,
    orbit_sign: f32,
}

// Returns orbital beta, gravitational lapse, and orbit direction in one pass.
// h_r: local H/R used to derive the sub-Keplerian factor for thick flows.
fn orbital_kerr(r_disk: f32, h_r: f32, a: f32) -> OrbitalResult {
    let a2 = a * a;
    let orbit_sign = select(-1.0, 1.0, a >= 0.0);
    let rho_k = max(r_disk / BH_M, 1.0);
    let omega_kep   = orbit_sign / (BH_M * max(rho_k * sqrt(rho_k) + orbit_sign * abs(a), 1.0e-4));
    let omega_orbit = omega_kep * sub_keplerian_factor(h_r);

    // Equatorial Kerr: sin(theta)^2 = 1 and cos(theta) = 0, so sigma = rho^2.
    let rho_m = metric_rho(r_disk);
    let rho2 = rho_m * rho_m;
    let delta = max(rho2 - 2.0 * rho_m + a2, DELTA_FLOOR);
    let rr_aa = rho2 + a2;
    let big_a = rr_aa * rr_aa - a2 * delta;
    let omega_drag = 2.0 * a * rho_m / max(BH_M * big_a, 1.0e-6);
    let lapse = max(sqrt(max(rho2 * delta / max(big_a, 1.0e-6), 0.0)), 1.0e-4);
    let g_phiphi = (BH_M * BH_M) * big_a / rho2;
    let beta = clamp(abs((omega_orbit - omega_drag) * sqrt(max(g_phiphi, 0.0)) / lapse), 0.0, 0.95);
    return OrbitalResult(beta, lapse, orbit_sign);
}

// r_disk: cylindrical radius already computed by caller.
// h_r:    local H/R already computed by caller.
fn shade_disk(ray: Ray, r_disk: f32, h_r: f32, a: f32) -> vec4<f32> {
    // Model-dependent emissivity colour.
    var base: vec3<f32>;
    if disk.model == 1u {
        // TruncHot: blend NT thermal (outer) with hot-flow synchrotron (inner).
        let safe_r  = max(r_disk,       SAGA_RS * 1.0e-3);
        let safe_rt = max(disk.r_trunc, SAGA_RS * 1.0e-3);
        let t = clamp((log(safe_r) - log(safe_rt)) / 0.4, -10.0, 10.0);
        let w     = 0.5 * (1.0 + tanh(t));   // 1 in outer thin disk, 0 in inner hot flow
        let c_nt  = blackbody_color(nt_temp(r_disk) / 0.488);
        let c_hot = hot_blackbody_color(hot_emissivity_t(r_disk));
        base = w * c_nt + (1.0 - w) * c_hot;
    } else {
        base = blackbody_color(nt_temp(r_disk) / 0.488);
    }

    let orb = orbital_kerr(r_disk, h_r, a);
    let inv_r_disk = 1.0 / max(r_disk, 1.0);
    let orbital = orb.orbit_sign * vec3<f32>(-ray.z * inv_r_disk, 0.0, ray.x * inv_r_disk);

    let to_cam = -ray_cart_dir(ray, a);
    let cos_alpha = dot(orbital, to_cam);

    let gamma = 1.0 / sqrt(max(1.0 - orb.beta * orb.beta, 1.0e-6));
    let doppler_kin = 1.0 / max(gamma * (1.0 - orb.beta * cos_alpha), 1.0e-4);
    let doppler = doppler_kin * orb.lapse;

    let doppler_clamped = clamp(doppler, 0.05, 8.0);
    let bright = doppler_clamped * doppler_clamped * doppler_clamped;
    let shift = clamp((doppler - 1.0) * 2.0, -1.0, 1.0);
    let disk_c = clamp(
        base + vec3<f32>(-shift * 0.35, -shift * 0.1, shift * 0.55),
        vec3<f32>(0.0), vec3<f32>(1.0)
    ) * bright;
    let mapped = disk_c / (disk_c + vec3<f32>(1.0));
    let fade = disk_edge_fade(r_disk);

    return vec4<f32>(mapped * fade, fade);
}

// -- Skybox ------------------------------------------------------------------

// Equirectangular HDR sample with manual bilinear (texture is Rgba32Float
// and we can't rely on float32-filterable). Expects a normalised direction.
// Reinhard-tonemapped to [0, 1].
fn sample_skybox(dir: vec3<f32>) -> vec3<f32> {
    let dims_u = textureDimensions(skybox);
    let w = i32(dims_u.x);
    let h = i32(dims_u.y);
    let dims = vec2<f32>(f32(w), f32(h));

    let d = dir;
    let u = atan2(d.z, d.x) * (1.0 / (2.0 * PI)) + 0.5;
    let v = acos(clamp(d.y, -1.0, 1.0)) * (1.0 / PI);

    let px = u * dims.x - 0.5;
    let py = v * dims.y - 0.5;

    let floor_px = floor(px);
    let floor_py = floor(py);
    let x0_raw = i32(floor_px);
    let y0 = clamp(i32(floor_py), 0, h - 1);
    let x1_raw = x0_raw + 1;
    let y1 = clamp(y0 + 1, 0, h - 1);
    let fx = px - floor_px;
    let fy = py - floor_py;

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

// -- Debug heatmap -----------------------------------------------------------

// Maps t ∈ [0, 1] to a black→red→yellow→white gradient.
// t = 0 (few iterations) = black; t = 1 (10 000 iterations) = white.
fn heatmap_color(t: f32) -> vec3<f32> {
    return vec3<f32>(
        clamp(t * 3.0,       0.0, 1.0),
        clamp(t * 3.0 - 1.0, 0.0, 1.0),
        clamp(t * 3.0 - 2.0, 0.0, 1.0),
    );
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

    let spin_a = spin_clamped();
    let spin_a2 = spin_a * spin_a;
    let disk_r1_2 = disk.r1 * disk.r1;
    let disk_r2_2 = disk.r2 * disk.r2;

    var ray = init_ray(cam.pos, dir, spin_a);
    var prev_pos = vec3<f32>(ray.x, ray.y, ray.z);
    var color = vec4<f32>(0.0);

    var disk_rgb = vec3<f32>(0.0);
    var disk_alpha = 0.0;
    var disk_accum = 0.0;
    var any_disk = false;

    var hit_black_hole = false;
    var hit_object = false;
    var obj_hit: ObjectHit;
    var passed_ergosphere = false;
    var ergosphere_alpha = 0.0;
    var iter_count: u32 = 0u;

    for (var i = 0; i < 10000; i++) {
        iter_count = u32(i) + 1u;
        if ray.r <= disk.horizon_r {
            hit_black_hole = true;
            break;
        }

        let static_limit = kerr_static_limit(ray.theta, spin_a2);
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
        ray = step_ray(ray, dL, spin_a);

        let new_pos = vec3<f32>(ray.x, ray.y, ray.z);

        if disk_accum < 2.5 && disk_alpha < 0.995 {
            let r_xz2 = new_pos.x * new_pos.x + new_pos.z * new_pos.z;
            if r_xz2 >= disk_r1_2 && r_xz2 <= disk_r2_2 {
                let r_xz = sqrt(r_xz2);
                let phi   = atan2(new_pos.z, new_pos.x);
                let h_r   = get_h_over_r(r_xz);
                let H     = h_r * r_xz;
                let y_mid = disk_midplane_y(r_xz, phi);   // 0 for all models except Warped
                let z_norm = (new_pos.y - y_mid) / max(H, 1.0e-4 * SAGA_RS);
                if abs(z_norm) < 4.0 {
                    let density = exp(-0.5 * z_norm * z_norm);
                    // Normaliser 0.4 ≈ 1/√(2π) so a perpendicular crossing totals ~1.
                    let ds = length(new_pos - prev_pos);
                    let contrib = density * ds / max(H, 1.0e-4 * SAGA_RS) * 0.4;
                    if contrib > 1.0e-5 {
                        let c = shade_disk(ray, r_xz, h_r, spin_a);
                        let w = min(contrib, 2.5 - disk_accum);
                        disk_accum += w;
                        let sample_alpha = clamp(c.a * (1.0 - exp(-0.7 * w)), 0.0, 0.98);
                        if sample_alpha > 1.0e-5 {
                            let remaining = 1.0 - disk_alpha;
                            disk_rgb += remaining * c.rgb * sample_alpha;
                            disk_alpha += remaining * sample_alpha;
                            any_disk = true;
                        }
                    }
                }
            }
        }

        obj_hit = intersect_objects(new_pos);
        if obj_hit.hit { hit_object = true; break; }

        prev_pos = new_pos;
        if ray.r > ESCAPE_R { break; }
    }

    if cam.debug_heatmap != 0u {
        let t = f32(iter_count) / 10000.0;
        textureStore(out_image, pix, vec4<f32>(heatmap_color(t), 1.0));
        return;
    }

    var scene_rgb: vec3<f32>;
    if hit_black_hole {
        scene_rgb = vec3<f32>(0.0);
    } else if hit_object {
        let p = vec3<f32>(ray.x, ray.y, ray.z);
        let n = normalize(p - obj_hit.center);
        let view = normalize(cam.pos - p);
        let diff = max(dot(n, view), 0.0);
        let intensity = 0.1 + 0.9 * diff;
        scene_rgb = obj_hit.color.rgb * intensity;
    } else {
        scene_rgb = sample_skybox(ray_cart_dir(ray, spin_a));
        if passed_ergosphere {
            scene_rgb = mix(scene_rgb, vec3<f32>(0.95, 0.42, 0.08), 0.18 * ergosphere_alpha);
        }
    }

    if any_disk {
        scene_rgb = disk_rgb + (1.0 - disk_alpha) * scene_rgb;
    }
    color = vec4<f32>(scene_rgb, 1.0);

    textureStore(out_image, pix, color);
}
