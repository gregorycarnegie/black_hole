//! Separated (Carter-constant) solution of null geodesics around an isolated Kerr
//! hole in binary64, as an independent reference for the numerical renderer
//! (checklist P1.7). Uncertified.
//!
//! Conventions match the renderer: unit mass at the origin, spin `a` along +y,
//! ingoing Kerr–Schild Cartesian coordinates (x, y, z) and covariant momentum
//! (p_t, p_x, p_y, p_z). Internally the spin axis is Z with (X, Y, Z) = (z, x, y), so
//! X + iY = (r + ia) e^{iφ} sin θ and Z = r cos θ, with φ the Kerr–Schild azimuth.
//! Mino time τ is normalised by |E|: dr/dτ = ±√R and dθ/dτ = ±√Θ with
//! R = (r² + a² - aλ)² - Δ(η + (λ - a)²), Θ = η + a² cos²θ - λ² cot²θ, λ = L/E, η = Q/E².

mod elliptic;
mod escape;
mod quadrature;

use crate::certified::Kerr;
use elliptic::{amplitude, legendre_f, legendre_pi, legendre_pi_near_one};
pub use escape::{End, Leg, sin_cos, vacuum_leg};
use quadrature::tanh_sinh;

/// Why a ray has no reference answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unresolved {
    /// The state is not outside the horizon, not null or not finite.
    InvalidInput,
    /// An escaping ray with Q <= 0 (vortical or equatorial polar motion).
    Vortical,
    /// Within reach of the pole, where the azimuth is ill-conditioned.
    Polar,
    /// The radial turning point is within the double-root tolerance of another root:
    /// the ray is too close to the critical curve to classify.
    Critical,
    /// Trapped between two radial turning points outside the horizon.
    Bound,
    /// The closed-form path does not cover this root configuration.
    Unsupported,
}

/// Which formulation evaluates the Mino-time integrals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Method {
    /// Legendre elliptic integrals and Jacobi functions (Gralla–Lupsasca form).
    Elliptic,
    /// Tanh–sinh quadrature of the same integrals, with the polar motion inverted
    /// by bisection.
    Quadrature,
}

/// Where the ray goes.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Outcome {
    /// It reaches the horizon.
    Captured,
    /// Its state where it first reaches the target radius going outward.
    Arrived {
        position: [f64; 3],
        momentum: [f64; 4],
    },
}

/// The conserved quantities of a ray: energy E = -p_t, axial angular momentum L and
/// Carter constant Q.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Constants {
    pub energy: f64,
    pub angular: f64,
    pub carter: f64,
}

/// A state in Boyer–Lindquist-like spheroidal form.
#[derive(Clone, Copy, Debug)]
struct Spheroidal {
    r: f64,
    cos: f64,
    sin: f64,
    phi: f64,
    /// Covariant Kerr–Schild p_r.
    p_r: f64,
    p_theta: f64,
}

fn spheroidal(a: f64, pos: [f64; 3], p: [f64; 4]) -> Spheroidal {
    let [x, y, z] = pos;
    let (big_x, big_y, big_z) = (z, x, y);
    let (p_x, p_y, p_z) = (p[3], p[1], p[2]);
    let rho2 = big_x * big_x + big_y * big_y;
    let q = rho2 + big_z * big_z - a * a;
    let r = (0.5 * (q + (q * q + 4.0 * a * a * big_z * big_z).sqrt())).sqrt();
    let cos = big_z / r;
    let sin = (rho2 / (r * r + a * a)).sqrt();
    let phi = big_y.atan2(big_x) - a.atan2(r);
    let (sp, cp) = phi.sin_cos();
    Spheroidal {
        r,
        cos,
        sin,
        phi,
        p_r: sin * (cp * p_x + sp * p_y) + cos * p_z,
        p_theta: cos / sin * (big_x * p_x + big_y * p_y) - r * sin * p_z,
    }
}

/// E, L and Q of a ray.
pub fn constants(spin: f64, pos: [f64; 3], p: [f64; 4]) -> Constants {
    let s = spheroidal(spin, pos, p);
    let [x, _, z] = pos;
    let energy = -p[0];
    let angular = z * p[1] - x * p[3];
    let carter = s.p_theta * s.p_theta
        + s.cos * s.cos * (angular * angular / (s.sin * s.sin) - spin * spin * energy * energy);
    Constants {
        energy,
        angular,
        carter,
    }
}

// ---------------------------------------------------------------------------
// Radial potential

#[derive(Clone, Copy, Debug)]
struct Complex {
    re: f64,
    im: f64,
}

impl Complex {
    fn real(re: f64) -> Self {
        Self { re, im: 0.0 }
    }
    fn add(self, o: Self) -> Self {
        Self {
            re: self.re + o.re,
            im: self.im + o.im,
        }
    }
    fn sub(self, o: Self) -> Self {
        Self {
            re: self.re - o.re,
            im: self.im - o.im,
        }
    }
    fn mul(self, o: Self) -> Self {
        Self {
            re: self.re * o.re - self.im * o.im,
            im: self.re * o.im + self.im * o.re,
        }
    }
    fn div(self, o: Self) -> Self {
        let d = o.re * o.re + o.im * o.im;
        Self {
            re: (self.re * o.re + self.im * o.im) / d,
            im: (self.im * o.re - self.re * o.im) / d,
        }
    }
    fn scale(self, k: f64) -> Self {
        Self {
            re: self.re * k,
            im: self.im * k,
        }
    }
    fn abs(self) -> f64 {
        self.re.hypot(self.im)
    }
    fn arg(self) -> f64 {
        self.im.atan2(self.re)
    }
    fn polar(r: f64, t: f64) -> Self {
        Self {
            re: r * t.cos(),
            im: r * t.sin(),
        }
    }
    fn sqrt(self) -> Self {
        Self::polar(self.abs().sqrt(), 0.5 * self.arg())
    }
    fn cbrt(self) -> Self {
        Self::polar(self.abs().cbrt(), self.arg() / 3.0)
    }
}

/// The normalised radial quartic r⁴ + A r² + B r + C.
#[derive(Clone, Copy, Debug)]
struct Quartic {
    a: f64,
    b: f64,
    c: f64,
}

impl Quartic {
    fn new(spin: f64, lambda: f64, eta: f64) -> Self {
        Self {
            a: spin * spin - eta - lambda * lambda,
            b: 2.0 * (eta + (lambda - spin) * (lambda - spin)),
            c: -spin * spin * eta,
        }
    }

    fn eval(self, z: Complex) -> (Complex, Complex) {
        let z2 = z.mul(z);
        let value = z2
            .mul(z2)
            .add(z2.scale(self.a))
            .add(z.scale(self.b))
            .add(Complex::real(self.c));
        let slope = z2
            .mul(z)
            .scale(4.0)
            .add(z.scale(2.0 * self.a))
            .add(Complex::real(self.b));
        (value, slope)
    }

    /// The four roots by Ferrari's resolvent (Gralla & Lupsasca 2020, eq. 95), each
    /// polished by Newton's method.
    fn roots(self) -> [Complex; 4] {
        let (a, b, c) = (self.a, self.b, self.c);
        let p = -a * a / 12.0 - c;
        let q = -a / 3.0 * ((a / 6.0) * (a / 6.0) - c) - b * b / 8.0;
        let disc = Complex::real((p / 3.0).powi(3) + (q / 2.0) * (q / 2.0)).sqrt();
        let mut omega = Complex::real(-q / 2.0).add(disc).cbrt();
        if omega.abs() < 1.0e-300 {
            omega = Complex::real(-q / 2.0).sub(disc).cbrt();
        }
        let omega_minus = if omega.abs() < 1.0e-300 {
            Complex::real(0.0)
        } else {
            Complex::real(-p / 3.0).div(omega)
        };
        let z = omega
            .add(omega_minus)
            .sub(Complex::real(a / 3.0))
            .scale(0.5)
            .sqrt();
        let base = z.mul(z).scale(-1.0).sub(Complex::real(a / 2.0));
        let shift = if z.abs() < 1.0e-300 {
            Complex::real(0.0)
        } else {
            Complex::real(b / 4.0).div(z)
        };
        let lower = base.add(shift).sqrt();
        let upper = base.sub(shift).sqrt();
        let mut roots = [
            z.scale(-1.0).sub(lower),
            z.scale(-1.0).add(lower),
            z.sub(upper),
            z.add(upper),
        ];
        for root in &mut roots {
            for _ in 0..4 {
                let (value, slope) = self.eval(*root);
                if slope.abs() == 0.0 {
                    break;
                }
                *root = root.sub(value.div(slope));
            }
        }
        roots
    }
}

/// The roots sorted into real ones (ascending) and complex ones, or `Critical` when a
/// root is too close to the real axis to tell.
fn split_roots(roots: [Complex; 4], scale: f64) -> Result<(Vec<f64>, Vec<Complex>), Unresolved> {
    let mut reals = Vec::new();
    let mut complex = Vec::new();
    for root in roots {
        let im = root.im.abs();
        if im <= 1.0e-9 * scale {
            reals.push(root.re);
        } else if im <= 1.0e-6 * scale {
            return Err(Unresolved::Critical);
        } else {
            complex.push(root);
        }
    }
    reals.sort_by(f64::total_cmp);
    Ok((reals, complex))
}

/// The radial motion from the start to the target radius.
#[derive(Clone, Debug)]
struct Radial {
    roots: Vec<f64>,
    complex: Vec<Complex>,
    /// Turning point passed on the way out, if the ray starts inward.
    bounce: Option<f64>,
}

impl Radial {
    /// R(r) / ((r - turning point)) is never formed: the product uses every root.
    fn potential(&self, r: f64, distance_to_bounce: Option<f64>) -> f64 {
        let mut value = 1.0;
        for &root in &self.roots {
            value *= match (self.bounce, distance_to_bounce) {
                (Some(b), Some(d)) if b == root => d,
                _ => r - root,
            };
        }
        for pair in self.complex.chunks(2) {
            let c = pair[0];
            value *= (r - c.re) * (r - c.re) + c.im * c.im;
        }
        value
    }
}

// ---------------------------------------------------------------------------
// Propagation

struct Setup {
    spin: f64,
    s: Spheroidal,
    k: Constants,
    lambda: f64,
    eta: f64,
    horizon: f64,
    inner: f64,
}

fn setup(spin: f64, pos: [f64; 3], p: [f64; 4]) -> Result<Setup, Unresolved> {
    if !spin.is_finite()
        || spin.abs() >= 1.0
        || pos.iter().chain(&p).any(|v| !v.is_finite())
        || p[0] == 0.0
    {
        return Err(Unresolved::InvalidInput);
    }
    let s = spheroidal(spin, pos, p);
    let k = constants(spin, pos, p);
    let root = (1.0 - spin * spin).sqrt();
    let (horizon, inner) = (1.0 + root, 1.0 - root);
    if s.r.is_nan() || s.r <= horizon {
        return Err(Unresolved::InvalidInput);
    }
    Ok(Setup {
        spin,
        s,
        k,
        lambda: k.angular / k.energy,
        eta: k.carter / (k.energy * k.energy),
        horizon,
        inner,
    })
}

/// Follows the ray from `pos` with covariant momentum `p` until it is captured or
/// first reaches Kerr–Schild radius `target` moving outward.
pub fn propagate(
    spin: f64,
    pos: [f64; 3],
    p: [f64; 4],
    target: f64,
    method: Method,
) -> Result<Outcome, Unresolved> {
    let st = setup(spin, pos, p)?;
    let (a, s) = (st.spin, st.s);
    if target.is_nan() || target <= s.r {
        return Err(Unresolved::InvalidInput);
    }
    let delta = |r: f64| r * r - 2.0 * r + a * a;
    let lambda = st.lambda;
    // Boyer–Lindquist p_r; its sign is that of dr/dτ outside the horizon.
    let p_r_bl = s.p_r - (2.0 * s.r * st.k.energy - a * st.k.angular) / delta(s.r);
    let outward = p_r_bl > 0.0;

    let quartic = Quartic::new(a, lambda, st.eta);
    let scale = 1.0 + lambda.abs() + st.eta.abs().sqrt();
    let (reals, complex) = split_roots(quartic.roots(), scale)?;
    let below = reals.iter().copied().rfind(|&root| root <= s.r);
    let above = reals.iter().copied().find(|&root| root > s.r);
    if above.is_some() {
        return match below {
            Some(low) if low > st.horizon => Err(Unresolved::Bound),
            _ => Ok(Outcome::Captured),
        };
    }
    let bounce = if outward {
        None
    } else {
        match below {
            Some(low) if low > st.horizon => Some(low),
            _ => return Ok(Outcome::Captured),
        }
    };
    if let Some(turn) = bounce {
        let next = reals.iter().copied().rfind(|&root| root < turn);
        if next.is_some_and(|other| turn - other < 1.0e-7 * turn) {
            return Err(Unresolved::Critical);
        }
    }
    // shortcut: escaping rays with Q <= 0 need the vortical polar solution (Gralla &
    // Lupsasca 2020, eq. 30); add it if the GPU comparison meets them.
    if st.k.carter.is_nan() || st.k.carter <= 0.0 {
        return Err(Unresolved::Vortical);
    }
    let radial = Radial {
        roots: reals,
        complex,
        bounce,
    };

    let (mino, phi_radial) = match method {
        Method::Elliptic => elliptic_radial(&st, &radial, target)?,
        Method::Quadrature => quadrature_radial(&st, &radial, target),
    };
    let polar = match method {
        Method::Elliptic => elliptic_polar(&st, mino)?,
        Method::Quadrature => quadrature_polar(&st, mino)?,
    };
    // Kerr–Schild azimuth: dφ = dφ_BL + a dr / Δ, signed along the path.
    let (rp, rm) = (st.horizon, st.inner);
    let log_ratio = |r: f64| ((r - rp) / (r - rm)).ln();
    let ks_shift = if a == 0.0 {
        0.0
    } else {
        a / (rp - rm) * (log_ratio(target) - log_ratio(s.r))
    };
    let sign_e = st.k.energy.signum();
    let phi = s.phi + sign_e * (phi_radial + lambda * polar.inverse_sine_square) + ks_shift;
    Ok(rebuild(&st, target, polar.cos, polar.cos_rate_sign, phi))
}

/// The polar end state and ∫ dτ / sin²θ.
struct Polar {
    cos: f64,
    /// Sign of d(cos θ)/dτ at the end.
    cos_rate_sign: f64,
    inverse_sine_square: f64,
}

/// u₊ = cos²θ at the polar turning points and 1 - u₊, each from its own quadratic so
/// both keep full precision (a²u² + (η + λ² - a²)u - η = 0, and with w = 1 - u,
/// a²w² - (η + λ² + a²)w + λ² = 0).
fn polar_root(st: &Setup) -> (f64, f64) {
    let a2 = st.spin * st.spin;
    let l2 = st.lambda * st.lambda;
    let beta = st.eta + l2 - a2;
    let u = 2.0 * st.eta / (beta + (beta * beta + 4.0 * a2 * st.eta).sqrt());
    let gamma = st.eta + l2 + a2;
    let w = 2.0 * l2 / (gamma + (gamma * gamma - 4.0 * a2 * l2).max(0.0).sqrt());
    (u, w)
}

/// Starting direction of cos θ along the ray.
fn cos_direction(st: &Setup) -> f64 {
    // dθ/dτ has the sign of p_θ, and cos θ moves the other way.
    if st.s.p_theta != 0.0 {
        -st.s.p_theta.signum()
    } else if st.s.cos != 0.0 {
        -st.s.cos.signum()
    } else {
        1.0
    }
}

fn elliptic_polar(st: &Setup, mino: f64) -> Result<Polar, Unresolved> {
    let (u, w) = polar_root(st);
    if w == 0.0 {
        return Err(Unresolved::Polar);
    }
    let top = u.sqrt();
    let m = -st.spin * st.spin * u * u / st.eta;
    let kappa = (st.eta / u).sqrt();
    let sign = cos_direction(st);
    let start = (st.s.cos / top).clamp(-1.0, 1.0).asin();
    let arg = sign * kappa * mino + legendre_f(start, m);
    let end = amplitude(arg, m);
    let integral =
        sign / kappa * (legendre_pi_near_one(u, w, end, m) - legendre_pi_near_one(u, w, start, m));
    Ok(Polar {
        cos: top * end.sin(),
        cos_rate_sign: sign * end.cos().signum(),
        inverse_sine_square: integral,
    })
}

fn quadrature_polar(st: &Setup, mino: f64) -> Result<Polar, Unresolved> {
    let (u, w) = polar_root(st);
    if w == 0.0 {
        return Err(Unresolved::Polar);
    }
    let top = u.sqrt();
    // 1 - top = w / (1 + top), exact where 1 - top would cancel.
    let gap = w / (1.0 + top);
    let (a2, eta) = (st.spin * st.spin, st.eta);
    // P(c) = (u₊ - c²)(η/u₊ + a² c²) with the turning-point factors taken from the
    // exact distances when an endpoint is a turning point.
    let integrals = |from: f64, to: f64| {
        let factor = |c: f64, da: f64, db: f64, end: f64| {
            if from == end {
                da
            } else if to == end {
                db
            } else {
                (end - c).abs()
            }
        };
        let g = |c: f64, da: f64, db: f64| {
            let p = factor(c, da, db, top) * factor(c, da, db, -top) * (eta / u + a2 * c * c);
            1.0 / p.sqrt()
        };
        let time = tanh_sinh(g, from, to).abs();
        // 1 - c² = (1 - c)(1 + c), with 1 ∓ c = gap + (distance to ±top).
        let sine = tanh_sinh(
            |c, da, db| {
                let near = |end: f64| gap + factor(c, da, db, end);
                g(c, da, db) / (near(top) * near(-top))
            },
            from,
            to,
        )
        .abs();
        (time, sine)
    };
    let mut sign = cos_direction(st);
    let mut c = (st.s.cos).clamp(-top, top);
    let mut remaining = mino;
    let mut sine_total = 0.0;
    let (half_time, half_sine) = integrals(-top, top);
    loop {
        let turn = sign * top;
        let (time, sine) = integrals(c, turn);
        if remaining <= time {
            break;
        }
        remaining -= time;
        sine_total += sine;
        c = turn;
        sign = -sign;
        let halves = (remaining / half_time).floor();
        if halves >= 1.0 {
            remaining -= halves * half_time;
            sine_total += halves * half_sine;
            if halves % 2.0 == 1.0 {
                c = -c;
                sign = -sign;
            }
        }
    }
    let (mut lo, mut hi) = (c, sign * top);
    for _ in 0..80 {
        let mid = 0.5 * (lo + hi);
        if integrals(c, mid).0 < remaining {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let end = 0.5 * (lo + hi);
    Ok(Polar {
        cos: end,
        cos_rate_sign: sign,
        inverse_sine_square: sine_total + integrals(c, end).1,
    })
}

/// Mino time and the radial azimuth integral ∫ a(2r - aλ) / Δ dτ.
fn quadrature_radial(st: &Setup, radial: &Radial, target: f64) -> (f64, f64) {
    let a = st.spin;
    let lambda = st.lambda;
    let segment = |from: f64, to: f64| {
        let touches = radial.bounce == Some(from);
        let w = |r: f64, da: f64, _| {
            let rr = radial.potential(r, touches.then_some(da));
            1.0 / rr.sqrt()
        };
        let time = tanh_sinh(w, from, to);
        let phi = tanh_sinh(
            |r, da, db| a * (2.0 * r - a * lambda) / (r * r - 2.0 * r + a * a) * w(r, da, db),
            from,
            to,
        );
        (time, phi)
    };
    match radial.bounce {
        Some(turn) => {
            let (t1, p1) = segment(turn, st.s.r);
            let (t2, p2) = segment(turn, target);
            (t1 + t2, p1 + p2)
        }
        None => segment(st.s.r, target),
    }
}

/// The closed forms for four real roots r₁ < r₂ < r₃ < r₄ on r >= r₄ (Gralla &
/// Lupsasca 2020, case 2): Mino time and the radial azimuth integral from r₄.
fn elliptic_radial(st: &Setup, radial: &Radial, target: f64) -> Result<(f64, f64), Unresolved> {
    let [_, _, r3, r4] = radial.roots[..] else {
        return Err(Unresolved::Unsupported);
    };
    // shortcut: outgoing rays whose largest root is inside the horizon (cases 2–4
    // without a turning point) are left to the quadrature; add the case 3/4 closed
    // forms when the GPU comparison needs outward camera rays.
    if r4 <= st.horizon {
        return Err(Unresolved::Unsupported);
    }
    let r1 = radial.roots[0];
    let (r31, r41, r32, r42, r43) = (
        r3 - r1,
        r4 - r1,
        r3 - radial.roots[1],
        r4 - radial.roots[1],
        r4 - r3,
    );
    let m = r32 * r41 / (r31 * r42);
    let g = 2.0 / (r31 * r42).sqrt();
    let a = st.spin;
    let (rp, rm) = (st.horizon, st.inner);
    let amp = |r: f64| (r31 * (r - r4) / (r41 * (r - r3))).sqrt().asin();
    let from_turn = |r: f64| {
        let phi = amp(r);
        let f = legendre_f(phi, m);
        let third = |root: f64| {
            let (r3x, r4x) = (r3 - root, r4 - root);
            let n = r41 * r3x / (r31 * r4x);
            g * (f / r3x - r43 / (r3x * r4x) * legendre_pi(n, phi, m))
        };
        let azimuth = if a == 0.0 {
            0.0
        } else {
            let plus = a * (2.0 * rp - a * st.lambda) / (rp - rm);
            let minus = -a * (2.0 * rm - a * st.lambda) / (rp - rm);
            plus * third(rp) + minus * third(rm)
        };
        (g * f, azimuth)
    };
    let (t_end, p_end) = from_turn(target);
    let (t_start, p_start) = from_turn(st.s.r);
    Ok(if radial.bounce.is_some() {
        (t_end + t_start, p_end + p_start)
    } else {
        (t_end - t_start, p_end - p_start)
    })
}

/// The Cartesian state at radius `r` from its spheroidal parts; the ray moves outward.
fn rebuild(st: &Setup, r: f64, cos: f64, cos_rate_sign: f64, phi: f64) -> Outcome {
    let a = st.spin;
    let e = st.k.energy;
    let (lambda, eta) = (st.lambda, st.eta);
    let sin2 = (1.0 - cos * cos).max(0.0);
    let sin = sin2.sqrt();
    let delta = r * r - 2.0 * r + a * a;
    let radial = (r * r + a * a - a * lambda).powi(2) - delta * (eta + (lambda - a).powi(2));
    let polar = (eta + a * a * cos * cos - lambda * lambda * cos * cos / sin2).max(0.0);
    // p_θ has the sign of dθ/dτ, the opposite of d(cos θ)/dτ; Boyer–Lindquist p_r is
    // positive going out, and Kerr–Schild p_r adds (2rE - aL)/Δ.
    let p_theta = -cos_rate_sign * e.abs() * polar.sqrt();
    let p_r = e.abs() * radial.max(0.0).sqrt() / delta + (2.0 * r * e - a * st.k.angular) / delta;
    let (sp, cp) = phi.sin_cos();
    let big_x = (r * cp - a * sp) * sin;
    let big_y = (r * sp + a * cp) * sin;
    let big_z = r * cos;
    // Rows: ∂(X, Y, Z)/∂r, ∂θ, ∂φ. Solve Jᵀ p = (p_r, p_θ, L) by Cramer's rule.
    let j = [
        [cp * sin, sp * sin, cos],
        [(r * cp - a * sp) * cos, (r * sp + a * cp) * cos, -r * sin],
        [-(r * sp + a * cp) * sin, (r * cp - a * sp) * sin, 0.0],
    ];
    let rhs = [p_r, p_theta, st.k.angular];
    let det3 = |m: [[f64; 3]; 3]| {
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    };
    let det = det3(j);
    let solve = |col: usize| {
        let mut m = j;
        for row in 0..3 {
            m[row][col] = rhs[row];
        }
        det3(m) / det
    };
    let (p_x, p_y, p_z) = (solve(0), solve(1), solve(2));
    Outcome::Arrived {
        position: [big_y, big_z, big_x],
        momentum: [-e, p_y, p_z, p_x],
    }
}

/// Unit coordinate-velocity direction of a state, as the renderer samples the sky.
pub fn direction(spin: f64, pos: [f64; 3], p: [f64; 4]) -> [f64; 3] {
    let kerr = Kerr {
        spin: [0.0, spin, 0.0],
    };
    let mut state = [0.0; 11];
    state[..3].copy_from_slice(&pos);
    state[3..7].copy_from_slice(&p);
    let k = kerr.phase_rhs(state);
    let n = (k[0] * k[0] + k[1] * k[1] + k[2] * k[2]).sqrt();
    [k[0] / n, k[1] / n, k[2] / n]
}

#[cfg(test)]
mod tests;
