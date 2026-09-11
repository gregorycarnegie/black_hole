// Geodesic ray-tracer: null geodesics in Kerr spacetime.
// The Kerr spin axis is +Y, matching the accretion disk normal.

@group(0) @binding(0) var out_image: texture_storage_2d<rgba8unorm, write>;

struct Camera {
    pos:           vec3<f32>,
    _pad0:         f32,
    right:         vec3<f32>,
    _pad1:         f32,
    up:            vec3<f32>,
    _pad2:         f32,
    forward:       vec3<f32>,
    _pad3:         f32,
    tan_half_fov:  f32,
    aspect:        f32,
    moving:        u32,
    jitter_x:      f32,
    jitter_y:      f32,
    debug_heatmap: u32,
    max_iter:      u32,
    polarization_view: u32,
    frequency_ghz: f32,
    faraday_depth: f32,
    conversion_depth: f32,
    _pad7: f32,
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
    binary_enabled: u32,
    _pad0:     f32,
    _pad1:     f32,
    _pad2:     f32,
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
    // Per-object dimensionless spin vector a*.
    spin:        array<vec4<f32>, 16>,
}
@group(0) @binding(3) var<uniform> objects: Objects;

@group(0) @binding(4) var skybox: texture_2d<f32>;

// -- Constants ---------------------------------------------------------------
const PI: f32 = 3.141592653589793;
const SCHWARZSCHILD_RADIUS: f32 = 2.0;
const ESCAPE_R: f32 = 1600.0;

// Cartesian ingoing Kerr-Schild, signature (-,+,+,+), vector order (t,x,y,z).
// g = eta + sum(2 H l l^T). One source is exact Kerr outside excision.
// ponytail: frozen, unboosted superposition for separated binaries; use evolved
// numerical-relativity metric data for inspiral/merger or retarded-time imaging.
const ETA = mat4x4<f32>(vec4<f32>(-1,0,0,0), vec4<f32>(0,1,0,0),
                        vec4<f32>(0,0,1,0), vec4<f32>(0,0,0,1));

fn outer(a: vec4<f32>, b: vec4<f32>) -> mat4x4<f32> {
    return mat4x4<f32>(a*b.x, a*b.y, a*b.z, a*b.w);
}

fn kerr_radius(x: vec3<f32>, a: vec3<f32>) -> f32 {
    let q = dot(x,x) - dot(a,a);
    let ax = dot(a,x);
    let root = sqrt(q*q + 4.0*ax*ax);
    // Rationalized negative-q branch avoids cancellation near the Kerr disk.
    var r2 = 0.5 * (q + root);
    if q < 0.0 { r2 = 2.0*ax*ax / max(root-q, 1.0e-20); }
    return sqrt(max(r2, 1.0e-12));
}

struct Metric {
    g: mat4x4<f32>,
    inv: mat4x4<f32>,
    dx: mat4x4<f32>,
    dy: mat4x4<f32>,
    dz: mat4x4<f32>,
    clearance: f32,
    valid: bool,
}

fn flat_metric() -> Metric {
    var m: Metric;
    m.g = ETA;
    m.inv = ETA;
    m.clearance = ESCAPE_R;
    m.valid = true;
    return m;
}

fn add_kerr(base: Metric, x: vec3<f32>, mass: f32, spin: vec3<f32>) -> Metric {
    var m = base;
    if mass <= 0.0 { return m; }
    let a = mass * spin / max(1.0, length(spin)/0.999);
    let a2 = dot(a,a);
    let ax = dot(a,x);
    let raw_r = kerr_radius(x,a);
    let horizon = mass + sqrt(max(mass*mass-a2, 0.0));
    m.clearance = min(m.clearance, raw_r-horizon);
    // RK stages may enter excision; reject the step before using these values.
    let r = max(raw_r, 0.8*horizon);
    let r2 = r*r;
    let den = r2*r2 + ax*ax;
    let h = mass*r*r2/den;
    let numerator = r*x - cross(a,x) + (ax/r)*a;
    let ell = vec4<f32>(1.0, numerator/(r2+a2));
    let ll = outer(ell,ell);
    let dr = (r*x + (ax/r)*a) / max(2.0*r2-dot(x,x)+a2, 1.0e-12);
    var deriv: array<mat4x4<f32>,3>;
    for (var j=0u; j<3u; j++) {
        var ej = vec3<f32>(0.0);
        ej[j] = 1.0;
        let dh = h*(3.0*dr[j]/r - (4.0*r*r2*dr[j]+2.0*ax*a[j])/den);
        let dn = dr[j]*x + r*ej - cross(a,ej) + (a[j]/r-ax*dr[j]/r2)*a;
        let dl = vec4<f32>(0.0, (dn - ell.yzw*2.0*r*dr[j])/(r2+a2));
        deriv[j] = 2.0*dh*ll + 2.0*h*(outer(dl,ell)+outer(ell,dl));
    }
    m.g += 2.0*h*ll;
    m.dx += deriv[0]; m.dy += deriv[1]; m.dz += deriv[2];
    // Sherman-Morrison inverts the SUM, including inter-source cross terms.
    let raised = m.inv*ell;
    let divisor = 1.0 + 2.0*h*dot(ell,raised);
    if divisor <= 1.0e-6 { m.valid = false; return m; }
    m.inv -= (2.0*h/divisor)*outer(raised,raised);
    m.valid = m.valid && m.inv[0][0] < -1.0e-6;
    return m;
}

fn scene_metric(pos: vec3<f32>) -> Metric {
    var m = flat_metric();
    for (var i=0; i<objects.num_objects; i++) {
        m = add_kerr(m, pos-objects.pos_radius[i].xyz,
                     max(objects.mass[i].x,0.0), objects.spin[i].xyz);
    }
    return m;
}

fn spatial_metric(m: Metric) -> mat3x3<f32> {
    return mat3x3<f32>(m.g[1].yzw, m.g[2].yzw, m.g[3].yzw);
}

fn spatial_unit(v: vec3<f32>, gamma: mat3x3<f32>) -> vec3<f32> {
    return v * inverseSqrt(max(dot(v,gamma*v), 1.0e-20));
}

struct Ray {
    pos: vec3<f32>,
    p: vec4<f32>,       // covariant photon momentum; p_t conserved in frozen metric
    screen: vec4<f32>,  // parallel-transported horizontal polarization basis
}

fn init_ray(pos: vec3<f32>, dir: vec3<f32>, m: Metric) -> Ray {
    let gamma = spatial_metric(m);
    let forward = spatial_unit(cam.forward,gamma);
    let right = spatial_unit(cam.right-forward*dot(forward,gamma*cam.right),gamma);
    let up = spatial_unit(cam.up-forward*dot(forward,gamma*cam.up)
        -right*dot(right,gamma*cam.up),gamma);
    let n = spatial_unit(dot(dir,cam.forward)*forward + dot(dir,cam.right)*right
        + dot(dir,cam.up)*up,gamma);
    let lapse = inverseSqrt(-m.inv[0][0]);
    let shift = -m.inv[0].yzw/m.inv[0][0];
    // Past-directed null tangent with unit energy in the camera Eulerian frame.
    let k = vec4<f32>(-1.0/lapse, n+shift/lapse);
    let screen = spatial_unit(right-n*dot(n,gamma*right),gamma);
    return Ray(pos,m.g*k,vec4<f32>(0.0,screen));
}

struct Derivs { pos: vec3<f32>, p: vec4<f32>, screen: vec4<f32> }

fn geodesic_rhs(ray: Ray, m: Metric) -> Derivs {
    let k = m.inv*ray.p;
    let dg_k = k.y*m.dx + k.z*m.dy + k.w*m.dz;
    let dg_f = ray.screen.y*m.dx + ray.screen.z*m.dy + ray.screen.w*m.dz;
    let contracted = vec4<f32>(0.0, dot(k,m.dx*ray.screen),
        dot(k,m.dy*ray.screen),dot(k,m.dz*ray.screen));
    return Derivs(k.yzw,
        0.5*vec4<f32>(0.0,dot(k,m.dx*k),dot(k,m.dy*k),dot(k,m.dz*k)),
        -0.5*m.inv*(dg_k*ray.screen + dg_f*k - contracted));
}

fn rk_state(ray: Ray, d: Derivs, h: f32) -> Ray {
    return Ray(ray.pos+h*d.pos,ray.p+h*d.p,ray.screen+h*d.screen);
}

fn step_ray(ray: Ray, h: f32, m: Metric) -> Ray {
    let k1 = geodesic_rhs(ray,m);
    let r2 = rk_state(ray,k1,0.5*h);
    let k2 = geodesic_rhs(r2,scene_metric(r2.pos));
    let r3 = rk_state(ray,k2,0.5*h);
    let k3 = geodesic_rhs(r3,scene_metric(r3.pos));
    let r4 = rk_state(ray,k3,h);
    let k4 = geodesic_rhs(r4,scene_metric(r4.pos));
    return rk_state(ray,Derivs(k1.pos+2.0*k2.pos+2.0*k3.pos+k4.pos,
        k1.p+2.0*k2.p+2.0*k3.p+k4.p,
        k1.screen+2.0*k2.screen+2.0*k3.screen+k4.screen),h/6.0);
}

// Gauge-fix the transported screen to the local Eulerian observer. Adding a
// multiple of k leaves the physical polarization unchanged.
fn screen_frame(ray: Ray, m: Metric) -> mat3x3<f32> {
    let k = m.inv*ray.p;
    let shift = -m.inv[0].yzw/m.inv[0][0];
    let gamma = spatial_metric(m);
    let n = spatial_unit(k.yzw+shift*k.x,gamma);
    let f = ray.screen.yzw-k.yzw*(ray.screen.x/k.x);
    let e1 = spatial_unit(f-n*dot(n,gamma*f),gamma);
    let e2 = spatial_unit(cross(gamma*n,gamma*e1),gamma);
    return mat3x3<f32>(e1,e2,n);
}

// -- Polarized transfer ------------------------------------------------------
// S=(I,Q,U,V); dP/ds = rho x P - alpha P + j_P, P=(Q,U,V).
// Scalar absorption, no dichroism. The exact constant-cell solution stays
// bounded at large Faraday depth; foreground operators compose camera-outward.
fn faraday_rotation(rho: vec3<f32>, ds: f32) -> mat3x3<f32> {
    let w = length(rho);
    let axis = rho/max(w,1.0e-20);
    let angle = w*ds;
    let c = cos(angle); let s = sin(angle);
    let identity = mat3x3<f32>(vec3<f32>(1,0,0),vec3<f32>(0,1,0),vec3<f32>(0,0,1));
    let cross_matrix = mat3x3<f32>(vec3<f32>(0,axis.z,-axis.y),
        vec3<f32>(-axis.z,0,axis.x),vec3<f32>(axis.y,-axis.x,0));
    let aa = mat3x3<f32>(axis*axis.x,axis*axis.y,axis*axis.z);
    return c*identity+s*cross_matrix+(1.0-c)*aa;
}

fn absorption_integral(alpha: f32, ds: f32) -> f32 {
    let tau = alpha*ds;
    if abs(tau) < 1.0e-3 { return ds*(1.0-0.5*tau+tau*tau/6.0); }
    return (1.0-exp(-tau))/alpha;
}

fn polarized_cell(j: vec4<f32>, alpha: f32, rho: vec3<f32>, ds: f32) -> vec4<f32> {
    let integral = absorption_integral(alpha,ds);
    let w = length(rho);
    if w*ds < 1.0e-5 { return j*integral; }
    let axis = rho/w;
    let parallel = axis*dot(axis,j.yzw);
    let perpendicular = j.yzw-parallel;
    let e = exp(-alpha*ds);
    let angle = w*ds;
    let den = alpha*alpha+w*w;
    let ic = (alpha*(1.0-e*cos(angle))+w*e*sin(angle))/den;
    let is = (w*(1.0-e*cos(angle))-alpha*e*sin(angle))/den;
    return vec4<f32>(j.x*integral,
        integral*parallel+ic*perpendicular+is*cross(axis,perpendicular));
}

// -- Intersection tests ------------------------------------------------------

struct ObjectHit { hit: bool, color: vec4<f32>, center: vec3<f32>, radius: f32 }

fn intersect_objects_segment(start: vec3<f32>, end: vec3<f32>) -> ObjectHit {
    var result: ObjectHit;
    result.hit = false;
    let segment = end - start;
    let segment_len2 = max(dot(segment, segment), 1.0e-12);
    for (var i = 0; i < objects.num_objects; i++) {
        let center = objects.pos_radius[i].xyz;
        let radius = objects.pos_radius[i].w;
        let t = clamp(dot(center - start, segment) / segment_len2, 0.0, 1.0);
        let closest = start + segment * t;
        let offset = closest - center;
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
    let edge_width = max(0.06 * (disk.r2 - disk.r1), 0.35 * SCHWARZSCHILD_RADIUS);
    let inner = smoothstep(disk.r1, disk.r1 + edge_width, r_disk);
    let outer = 1.0 - smoothstep(disk.r2 - edge_width, disk.r2, r_disk);
    return clamp(inner * outer, 0.0, 1.0);
}

// Model-dependent H/R at cylindrical radius r_xz.
fn get_h_over_r(r_xz: f32) -> f32 {
    if disk.model == 1u {
        // TruncHot: tanh transition — h_hot inside r_trunc, h_thin outside.
        let safe_r  = max(r_xz,        SCHWARZSCHILD_RADIUS * 1.0e-3);
        let safe_rt = max(disk.r_trunc, SCHWARZSCHILD_RADIUS * 1.0e-3);
        let t = clamp((log(safe_r) - log(safe_rt)) / 0.4, -10.0, 10.0);
        let w = 0.5 * (1.0 + tanh(t));   // 0 deep inside, 1 far outside
        return w * disk.h_thin + (1.0 - w) * disk.h_hot;
    } else if disk.model == 2u {
        // Slim / super-Eddington: disk puffs up inward at r_trunc (used as r_puff).
        let r_puff = max(disk.r_trunc, SCHWARZSCHILD_RADIUS * 0.5);
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
    let r_bp_safe = max(disk.r_bp, SCHWARZSCHILD_RADIUS * 0.1);
    let ln_norm   = clamp(log(max(r_xz, SCHWARZSCHILD_RADIUS * 0.01) / r_bp_safe) / 0.5, -10.0, 10.0);
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

// -- Skybox ------------------------------------------------------------------

// ACES filmic curve fit by Krzysztof Narkowicz (CC0/MIT).
// https://knarkowicz.wordpress.com/2016/01/06/aces-filmic-tone-mapping-curve/
// ponytail: compact ACES approximation; use a full colour transform if grading needs it.
fn tonemap(hdr: vec3<f32>) -> vec3<f32> {
    // Limit extreme inputs before the polynomial to avoid floating-point overflow.
    let x = clamp(hdr, vec3<f32>(0.0), vec3<f32>(1.0e4));
    return clamp((x * (2.51 * x + vec3<f32>(0.03))) /
        (x * (2.43 * x + vec3<f32>(0.59)) + vec3<f32>(0.14)),
        vec3<f32>(0.0), vec3<f32>(1.0));
}

// Linear HDR bilinear sample: wrap longitude, clamp latitude at the poles.
// Manual filtering also works with non-filterable rgba32float skyboxes.
fn sample_skybox(dir: vec3<f32>) -> vec3<f32> {
    let dims = vec2<i32>(textureDimensions(skybox));
    let uv = vec2<f32>(atan2(dir.z, dir.x) / (2.0 * PI) + 0.5,
                       acos(clamp(dir.y, -1.0, 1.0)) / PI);
    let texel = uv * vec2<f32>(dims) - vec2<f32>(0.5);
    let base = vec2<i32>(floor(texel));
    let weight = fract(texel);
    let x0 = ((base.x % dims.x) + dims.x) % dims.x;
    let x1 = (x0 + 1) % dims.x;
    let y0 = clamp(base.y, 0, dims.y - 1);
    let y1 = clamp(base.y + 1, 0, dims.y - 1);
    let top = mix(textureLoad(skybox, vec2<i32>(x0, y0), 0).rgb,
                  textureLoad(skybox, vec2<i32>(x1, y0), 0).rgb, weight.x);
    let bottom = mix(textureLoad(skybox, vec2<i32>(x0, y1), 0).rgb,
                     textureLoad(skybox, vec2<i32>(x1, y1), 0).rgb, weight.x);
    return mix(top, bottom, weight.y);
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

struct Plasma {
    rgb: vec3<f32>,
    j: vec4<f32>,
    alpha: f32,
    rho: vec3<f32>,
    energy: f32,
}

fn sample_plasma(ray: Ray, m: Metric) -> Plasma {
    var plasma: Plasma;
    let r = length(ray.pos.xz);
    if r <= disk.r1 || r >= disk.r2 { return plasma; }
    let h_r = get_h_over_r(r);
    let height = max(h_r*r,1.0e-4);
    let z = (ray.pos.y-disk_midplane_y(r,atan2(ray.pos.z,ray.pos.x)))/height;
    if abs(z) >= 4.0 { return plasma; }
    let density = 0.4*exp(-0.5*z*z)*disk_edge_fade(r)/height;
    let k = m.inv*ray.p;
    // Circular flow around +Y; negative BH spin is retrograde to this disk.
    let omega = sub_keplerian_factor(h_r)/max(pow(r,1.5)+disk.spin,1.0e-3);
    let tangent = vec3<f32>(ray.pos.z,0.0,-ray.pos.x);
    var fluid = vec4<f32>(1.0,omega*tangent);
    let norm = dot(fluid,m.g*fluid);
    if norm < -1.0e-4 {
        fluid *= inverseSqrt(-norm);
    } else {
        let lapse = inverseSqrt(-m.inv[0][0]);
        fluid = -lapse*m.inv[0];
    }
    plasma.energy = max(dot(ray.p,fluid),1.0e-5);
    let redshift = clamp(1.0/plasma.energy,0.01,20.0);
    let freq_ratio = 230.0/max(cam.frequency_ghz/redshift,1.0);
    let frame = screen_frame(ray,m);
    var e1 = vec4<f32>(0.0,frame[0]);
    var e2 = vec4<f32>(0.0,frame[1]);
    e1 -= k*(dot(e1,m.g*fluid)/plasma.energy);
    e2 -= k*(dot(e2,m.g*fluid)/plasma.energy);
    // ponytail: prescribed toroidal field and p=3 electrons in arbitrary units;
    // replace with calibrated GRMHD plasma/thermal coefficients for science.
    var b = vec4<f32>(0.0,normalize(tangent));
    b += fluid*dot(b,m.g*fluid);
    b *= inverseSqrt(max(dot(b,m.g*b),1.0e-12));
    let bx = dot(b,m.g*e1); let by = dot(b,m.g*e2);
    let bparallel = -dot(b,m.g*k)/plasma.energy; // toward the observer
    let perpendicular2 = clamp(bx*bx+by*by,0.0,1.0);
    let evpa = vec2<f32>(by*by-bx*bx,-2.0*bx*by)/max(perpendicular2,1.0e-12);
    var hot = 0.0;
    if disk.model == 1u {
        hot = 0.5*(1.0-tanh(clamp(log(r/max(disk.r_trunc,0.001))/0.4,-10.0,10.0)));
    }
    let thermal = (1.0-hot)*blackbody_color(nt_temp(r)/0.488);
    let synch = hot*hot_emissivity_t(r)*perpendicular2*freq_ratio
        *vec3<f32>(1.0,0.65,0.3);
    let boost = redshift*redshift*redshift;
    plasma.rgb = density*boost*(thermal+synch);
    let intensity = dot(plasma.rgb,vec3<f32>(0.2126,0.7152,0.0722));
    let synch_i = density*boost*dot(synch,vec3<f32>(0.2126,0.7152,0.0722));
    plasma.j = vec4<f32>(intensity,0.75*synch_i*evpa,0.0);
    plasma.alpha = 0.7*density;
    let rotation = 2.0*cam.faraday_depth*density*bparallel*freq_ratio*freq_ratio;
    let conversion = cam.conversion_depth*density*perpendicular2*pow(freq_ratio,3.0);
    plasma.rho = vec3<f32>(conversion*evpa,rotation);
    return plasma;
}

fn polarization_color(stokes: vec4<f32>) -> vec3<f32> {
    if stokes.x <= 1.0e-8 { return vec3<f32>(0.0); }
    let pol = clamp(stokes.yzw/stokes.x,vec3<f32>(-1.0),vec3<f32>(1.0));
    if cam.polarization_view == 1u { return vec3<f32>(clamp(length(pol.xy),0.0,1.0)); }
    if cam.polarization_view == 2u {
        let angle = atan2(pol.y,pol.x);
        let hue = 0.5+0.5*cos(angle+vec3<f32>(0.0,-2.0*PI/3.0,2.0*PI/3.0));
        return hue*clamp(length(pol.xy),0.0,1.0);
    }
    var signed = pol.z;
    if cam.polarization_view == 3u { signed = pol.x; }
    if cam.polarization_view == 4u { signed = pol.y; }
    return abs(signed)*select(vec3<f32>(0.15,0.4,1.0),vec3<f32>(1.0,0.25,0.1),signed>=0.0);
}

@compute @workgroup_size(16,16,1)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let dims = textureDimensions(out_image);
    let pix = vec2<i32>(gid.xy);
    if any(gid.xy >= dims) { return; }
    let u = (2.0*(f32(pix.x)+0.5+cam.jitter_x)/f32(dims.x)-1.0)*cam.aspect*cam.tan_half_fov;
    let v = (1.0-2.0*(f32(pix.y)+0.5+cam.jitter_y)/f32(dims.y))*cam.tan_half_fov;
    let dir = normalize(u*cam.right-v*cam.up+cam.forward);
    var metric = scene_metric(cam.pos);
    if !metric.valid || metric.clearance <= 0.0 {
        textureStore(out_image,pix,vec4<f32>(0,0,0,1)); return;
    }
    var ray = init_ray(cam.pos,dir,metric);
    var rgb = vec3<f32>(0.0);
    var stokes = vec4<f32>(0.0);
    var transmission = 1.0;
    var foreground = faraday_rotation(vec3<f32>(0.0),0.0);
    var iterations = 0u;
    for (var i=0u; i<cam.max_iter; i++) {
        iterations = i+1u;
        if metric.clearance < 0.002 || !metric.valid { break; }
        let velocity = (metric.inv*ray.p).yzw;
        // Geometry-limited steps also resolve the thinnest disk crossing.
        var distance = clamp(0.12*metric.clearance,0.0002,32.0);
        let radius = length(ray.pos.xz);
        let height = max(get_h_over_r(max(radius,disk.r1))*max(radius,disk.r1),0.001);
        if radius > disk.r1-distance && radius < disk.r2+distance {
            let mid = disk_midplane_y(max(radius,0.001),atan2(ray.pos.z,ray.pos.x));
            let to_disk = max(abs(ray.pos.y-mid)-4.0*height,0.0);
            distance = min(distance,max(0.25*height,0.5*to_disk));
        }
        var h = distance/max(length(velocity),1.0e-6);
        var next: Ray;
        var next_metric: Metric;
        var accepted = false;
        for (var retry=0u; retry<6u; retry++) {
            next = step_ray(ray,h,metric);
            next_metric = scene_metric(next.pos);
            let null_error = abs(dot(next.p,next_metric.inv*next.p))
                /max(dot(next.p,next.p),1.0e-10);
            if next_metric.valid && all(abs(next.pos)<vec3<f32>(1.0e8))
                && all(abs(next.p)<vec4<f32>(1.0e8)) && null_error<2.0e-4 {
                accepted = true; break;
            }
            h *= 0.5;
        }
        if !accepted { break; } // failed/incomplete rays never masquerade as escaped sky
        let hit = intersect_objects_segment(ray.pos,next.pos);
        if hit.hit {
            let intensity = dot(hit.color.rgb,vec3<f32>(0.2126,0.7152,0.0722));
            rgb += transmission*hit.color.rgb;
            stokes.x += transmission*intensity;
            break;
        }
        // Midpoint cell coefficients, exact emission/absorption/Faraday cell solve.
        let middle = Ray(0.5*(ray.pos+next.pos),0.5*(ray.p+next.p),0.5*(ray.screen+next.screen));
        let plasma = sample_plasma(middle,scene_metric(middle.pos));
        let ds = h*plasma.energy; // proper path length in the emitting fluid frame
        if ds > 0.0 {
            let cell = polarized_cell(plasma.j,plasma.alpha,plasma.rho,ds);
            stokes += transmission*vec4<f32>(cell.x,foreground*cell.yzw);
            rgb += transmission*plasma.rgb*absorption_integral(plasma.alpha,ds);
            foreground = foreground*faraday_rotation(plasma.rho,ds);
            transmission *= exp(-plasma.alpha*ds);
        }
        ray = next; metric = next_metric;
        let frame = screen_frame(ray,metric);
        ray.screen = vec4<f32>(0.0,frame[0]);
        if length(ray.pos)>ESCAPE_R {
            let sky = sample_skybox(normalize((metric.inv*ray.p).yzw));
            rgb += transmission*sky;
            stokes.x += transmission*dot(sky,vec3<f32>(0.2126,0.7152,0.0722));
            break;
        }
        if transmission<0.001 { break; }
    }
    var output = tonemap(rgb);
    if cam.polarization_view != 0u { output = polarization_color(stokes); }
    if cam.debug_heatmap != 0u { output = heatmap_color(f32(iterations)/f32(max(cam.max_iter,1u))); }
    textureStore(out_image,pix,vec4<f32>(output,1.0));
}
