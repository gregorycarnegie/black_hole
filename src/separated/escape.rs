//! Analytic vacuum legs (checklist P1.8): from a state outside a sphere that encloses
//! all emission, the separated Kerr solution carries the ray to the sky sphere or back
//! to that sphere, with only `sqrt` and a hand-written `sin_cos`, so the CUDA kernel can
//! repeat it line for line (`analytic_vacuum_leg` in `tools/cuda/kernels.rs`).
//!
//! Outside r = 12 the radial factor f(u) = R / r⁴, u = 1/r, is either close to 1 or
//! decreasing and concave, so a leg has at most one radial turning point and it is a
//! simple root. Where f stays above 1/2 the radial Mino-time integrals are smooth in u
//! and a short Gauss–Legendre sum suffices; near a root u₁ the substitution u = u₁ - t²
//! removes the inverse square root. The polar direction moves on the unit sphere: its
//! great-circle motion is solved exactly, and RK4 integrates only the spin's small
//! perturbation (variation of constants). Rays near the pole are left to the numerical
//! integrator.

/// Gauss–Legendre nodes and weights on [-1, 1], positive half.
const GL_NODES: [f64; 4] = [
    0.183_434_642_495_649_8,
    0.525_532_409_916_329,
    0.796_666_477_413_626_7,
    0.960_289_856_497_536_3,
];
const GL_WEIGHTS: [f64; 4] = [
    0.362_683_783_378_362,
    0.313_706_645_877_887_3,
    0.222_381_034_453_374_5,
    0.101_228_536_290_376_3,
];

/// RK4 steps of the polar perturbation.
pub const POLAR_STEPS: usize = 16;
/// Below this f(u) at the deep end of a piece, the piece is summed in t with
/// u = u₁ - t² (f is cos² of the radial angle in flat space).
pub const RADIAL_FLOOR: f64 = 0.5;
/// Smallest sin²θ accepted at either end, where the azimuth and p_θ are formed.
pub const POLAR_FLOOR: f64 = 1.0e-6;
/// Smallest inner radius: beyond it f has at most one root, and it is simple.
pub const INNER_MIN: f64 = 12.0;

/// sin x and cos x for |x| up to about 1e9, from Taylor polynomials on [-π/4, π/4].
pub fn sin_cos(x: f64) -> (f64, f64) {
    const PIO2_LO: f64 = 6.123_233_995_736_766e-17;
    let k = (x * std::f64::consts::FRAC_2_PI + if x >= 0.0 { 0.5 } else { -0.5 }) as i64;
    let kf = k as f64;
    let r = (x - kf * std::f64::consts::FRAC_PI_2) - kf * PIO2_LO;
    let r2 = r * r;
    // Horner forms of the series to r¹⁷ and r¹⁶; the next terms are below 2e-17.
    let s = r
        * (1.0
            + r2 * (-1.0 / 6.0
                + r2 * (1.0 / 120.0
                    + r2 * (-1.0 / 5040.0
                        + r2 * (1.0 / 362_880.0
                            + r2 * (-1.0 / 39_916_800.0
                                + r2 * (1.0 / 6_227_020_800.0
                                    + r2 * (-1.0 / 1_307_674_368_000.0
                                        + r2 / 355_687_428_096_000.0))))))));
    let c = 1.0
        + r2 * (-0.5
            + r2 * (1.0 / 24.0
                + r2 * (-1.0 / 720.0
                    + r2 * (1.0 / 40_320.0
                        + r2 * (-1.0 / 3_628_800.0
                            + r2 * (1.0 / 479_001_600.0
                                + r2 * (-1.0 / 87_178_291_200.0 + r2 / 20_922_789_888_000.0)))))));
    match k & 3 {
        0 => (s, c),
        1 => (c, -s),
        2 => (-s, -c),
        _ => (-c, s),
    }
}

/// Which boundary a vacuum leg ends on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum End {
    /// Radius `target`, going out.
    Sky,
    /// Radius `inner`, going in.
    Inner,
    /// The polar band |cos θ| = `band` around the equator.
    Band,
}

/// Where a vacuum leg ends.
#[derive(Clone, Copy, Debug)]
pub struct Leg {
    pub position: [f64; 3],
    pub momentum: [f64; 4],
    pub end: End,
    /// The radius increases at the end.
    pub outgoing: bool,
    /// Angle swept by the polar direction, for the renderer's winding count.
    pub arc: f64,
}

/// The radial integrands at piece coordinate x: x = u, or x = t with u = u₁ - t² when
/// `root` = (u₁, q) and f = (u - u₁) q(u). Returns u, the Mino-time rate dτ/dx and
/// f (or -q u₁, about 1 + u / u₁), which must stay above `RADIAL_FLOOR`.
fn radial_rate(x: f32, root: Option<(f64, [f64; 4])>, [fa, fb, fc]: [f32; 3]) -> (f32, f32, f32) {
    match root {
        Some((u1, q)) => {
            let u = u1 as f32 - x * x;
            let g = -(q[0] as f32 + u * (q[1] as f32 + u * (q[2] as f32 + u * q[3] as f32)));
            (u, 2.0 / g.sqrt(), g * u1 as f32)
        }
        None => {
            let fu = 1.0 + x * x * (fa + x * (fb + x * fc));
            (x, 1.0 / fu.sqrt(), fu)
        }
    }
}

/// Mino time and ∫ a(2r - aλ)/Δ dτ over piece coordinates `from` to `to`, both
/// positive, with binary32 sums as on the GPU.
fn piece_sum(
    (from, to): (f64, f64),
    root: Option<(f64, [f64; 4])>,
    coefficients: [f32; 3],
    (a, lambda): (f32, f32),
) -> Option<(f64, f64)> {
    let (mid, half) = (0.5 * (to + from), 0.5 * (to - from).abs());
    let (mid32, half32) = (mid as f32, half as f32);
    let (mut mino, mut phi, mut floor) = (0.0_f32, 0.0_f32, 1.0_f32);
    for (node, weight) in GL_NODES.iter().zip(GL_WEIGHTS) {
        for side in [-1.0_f32, 1.0] {
            let (u, rate, size) =
                radial_rate(mid32 + side * half32 * *node as f32, root, coefficients);
            floor = floor.min(size);
            let w = weight as f32 * rate;
            mino += w;
            phi += w * a * u * (2.0 - a * lambda * u) / (1.0 - 2.0 * u + a * a * u * u);
        }
    }
    (f64::from(floor) > RADIAL_FLOOR).then(|| (f64::from(mino) * half, f64::from(phi) * half))
}

/// Mino time until |cos θ| first falls to `band`, from cos θ = `cos` moving at
/// d(cos θ)/dτ = `rate`. (d cos θ / dτ)² = M = (μ₊² - cos²θ)(η / μ₊² + a² cos²θ), and
/// t = √(μ₊ - |cos θ|) removes the turning point. Infinite for vortical rays (η < 0)
/// that stay outside the band; `None` for the others and for a start inside the band.
#[allow(
    clippy::neg_cmp_op_on_partial_ord,
    reason = "NaN must fail every guard"
)]
fn band_time(cos: f64, rate: f64, band: f64, (a2, lambda, eta): (f64, f64, f64)) -> Option<f64> {
    let beta = eta + lambda * lambda - a2;
    if !(eta > 0.0) {
        // Vortical: |cos θ| stays at or above μ₋, the smaller root of M.
        let root = (beta * beta + 4.0 * a2 * eta).sqrt();
        let low = -2.0 * eta / (root - beta);
        return (low >= band * band).then_some(f64::INFINITY);
    }
    let up = 2.0 * eta / (beta + (beta * beta + 4.0 * a2 * eta).sqrt());
    let top = up.sqrt();
    let start = cos.abs().min(top);
    if !(start > band) {
        return None;
    }
    let (scale, top32, a2_32) = ((eta / up) as f32, top as f32, a2 as f32);
    // ∫ dμ / √M from |cos θ| = lo to hi <= μ₊.
    let integral = |lo: f64, hi: f64| {
        let (t_lo, t_hi) = ((top - hi).max(0.0).sqrt(), (top - lo).sqrt());
        let (mid, half) = ((0.5 * (t_hi + t_lo)) as f32, (0.5 * (t_hi - t_lo)) as f32);
        let mut sum = 0.0_f32;
        for (node, weight) in GL_NODES.iter().zip(GL_WEIGHTS) {
            for side in [-1.0_f32, 1.0] {
                let t = mid + side * half * *node as f32;
                let mu = top32 - t * t;
                sum += weight as f32 * 2.0 / ((top32 + mu) * (scale + a2_32 * mu * mu)).sqrt();
            }
        }
        f64::from(sum * half)
    };
    // Toward the equator directly, or out to μ₊ and back.
    Some(if cos * rate <= 0.0 {
        integral(band, start)
    } else {
        integral(start, top) + integral(band, top)
    })
}

/// The end of the vacuum leg from `pos` with covariant momentum `p` (conventions of
/// [`super::propagate`]): Kerr–Schild radius `target` going out, radius `inner` going
/// in, or, when `band` > 0, the band |cos θ| <= `band` around the equator, whichever
/// the ray reaches first. `None` unless [`INNER_MIN`] <= `inner` < r < `target` and
/// the start is outside the band, or when a guard rejects the ray.
#[allow(
    clippy::neg_cmp_op_on_partial_ord,
    reason = "NaN must fail every guard"
)]
pub fn vacuum_leg(
    spin: f64,
    pos: [f64; 3],
    p: [f64; 4],
    inner: f64,
    target: f64,
    band: f64,
) -> Option<Leg> {
    let a = spin;
    let a2 = a * a;
    let [x, y, z] = pos;
    // Spin axis Z: (X, Y, Z) = (z, x, y).
    let (big_x, big_y, big_z) = (z, x, y);
    let (p_x, p_y, p_z) = (p[3], p[1], p[2]);
    let rho2 = big_x * big_x + big_y * big_y;
    let q = rho2 + big_z * big_z - a2;
    let r2 = 0.5 * (q + (q * q + 4.0 * a2 * big_z * big_z).sqrt());
    let r = r2.sqrt();
    let cos = big_z / r;
    let sin2 = rho2 / (r2 + a2);
    // NaN-safe: every guard is written so that NaN fails it.
    if !(inner >= INNER_MIN && inner < r && r < target && sin2 > POLAR_FLOOR && a2 < 1.0) {
        return None;
    }
    let sin = sin2.sqrt();
    // e^{iφ} = (X + iY)(r - ia) / ((r² + a²) sin θ).
    let norm = 1.0 / ((r2 + a2) * sin);
    let (cp, sp) = (
        (big_x * r + big_y * a) * norm,
        (big_y * r - big_x * a) * norm,
    );
    let p_r = sin * (cp * p_x + sp * p_y) + cos * p_z;
    let p_theta = cos / sin * (big_x * p_x + big_y * p_y) - r * sin * p_z;
    let energy = -p[0];
    let angular = z * p[1] - x * p[3];
    let carter = p_theta * p_theta + cos * cos * (angular * angular / sin2 - a2 * energy * energy);
    let lambda = angular / energy;
    let eta = carter / (energy * energy);
    let e_abs = energy.abs();
    let delta = r2 - 2.0 * r + a2;
    // Boyer–Lindquist p_r is positive going out.
    let outward = p_r - (2.0 * r * energy - a * angular) / delta > 0.0;

    let (fa, fb, fc) = (
        a2 - eta - lambda * lambda,
        2.0 * (eta + (lambda - a) * (lambda - a)),
        -a2 * eta,
    );
    let f = |u: f64| {
        let u2 = u * u;
        1.0 + u2 * (fa + u * (fb + u * fc))
    };
    let (u_sky, u_start, u_inner) = (1.0 / target, 1.0 / r, 1.0 / inner);
    // f decreases beyond the start, so an inward ray turns before the sphere exactly
    // when f(u_inner) <= 0.
    let turning = !outward && !(f(u_inner) > 0.0);
    let escaped = outward || turning;
    let hi = if outward { u_start } else { u_inner };
    // The root u₁ at or just beyond `hi`, by Newton's method from about 1/b. f is
    // concave there, so the iterates approach it from above after the first.
    let root = if turning || !(f(hi) > RADIAL_FLOOR) {
        let start = if turning { u_start } else { hi };
        let mut u1 = f64::max(1.0 / (-fa).max(1.0e-30).sqrt(), start);
        // Binary32 iterations to about 1e-7, then two binary64 ones.
        let [fa32, fb32, fc32] = [fa as f32, fb as f32, fc as f32];
        let mut v = u1 as f32;
        for _ in 0..8 {
            let value = 1.0 + v * v * (fa32 + v * (fb32 + v * fc32));
            let slope = v * (2.0 * fa32 + v * (3.0 * fb32 + 4.0 * fc32 * v));
            v -= value / slope;
        }
        u1 = f64::from(v);
        for _ in 0..2 {
            u1 -= f(u1) / (u1 * (2.0 * fa + u1 * (3.0 * fb + 4.0 * fc * u1)));
        }
        let bracket = if turning {
            u_start <= u1 && u1 <= u_inner
        } else {
            hi < u1
        };
        if !(bracket && f(u1).abs() < 1.0e-12) {
            return None;
        }
        // f = (u - u₁) q(u) + f(u₁) by synthetic division.
        let q3 = fc;
        let q2 = fb + u1 * q3;
        let q1 = fa + u1 * q2;
        let q0 = u1 * q1;
        Some((u1, [q0, q1, q2, q3]))
    } else {
        None
    };
    let coefficients = [fa as f32, fb as f32, fc as f32];
    let constants = (a as f32, lambda as f32);
    // The path in piece coordinates: one piece, or in to the turning point and out.
    let coordinate = |u: f64| match root {
        Some((u1, _)) => (u1 - u).max(0.0).sqrt(),
        None => u,
    };
    let (pieces, outgoing) = if turning {
        (
            [(coordinate(u_start), 0.0), (0.0, coordinate(u_sky))],
            [false, true],
        )
    } else {
        let end = if outward { u_sky } else { u_inner };
        (
            [(coordinate(u_start), coordinate(end)), (0.0, 0.0)],
            [outward, outward],
        )
    };
    let count = if turning { 2 } else { 1 };
    let mut times = [0.0; 2];
    let mut phis = [0.0; 2];
    for k in 0..count {
        (times[k], phis[k]) = piece_sum(pieces[k], root, coefficients, constants)?;
    }
    let theta_rate = p_theta / e_abs;
    let polar = if band > 0.0 {
        band_time(cos, -sin * theta_rate, band, (a2, lambda, eta))?
    } else {
        f64::INFINITY
    };
    let (mut end, mut mino, mut phi_radial) = (
        if escaped { End::Sky } else { End::Inner },
        times[0] + times[1],
        phis[0] + phis[1],
    );
    let mut u_end = if escaped { u_sky } else { u_inner };
    let mut outgoing_end = escaped;
    if polar < mino {
        // The band comes first: find the piece coordinate where the Mino time is `polar`
        // by Newton's method on the partial sums.
        let k = usize::from(turning && polar > times[0]);
        let before = if k == 1 { times[0] } else { 0.0 };
        let (from, to) = pieces[k];
        let wanted = polar - before;
        let direction = if to > from { 1.0 } else { -1.0 };
        let mut x = from + (to - from) * (wanted / times[k]);
        for _ in 0..4 {
            let (time, _) = piece_sum((from, x), root, coefficients, constants)?;
            let (_, rate, _) = radial_rate(x as f32, root, coefficients);
            x = (x - direction * (time - wanted) / f64::from(rate))
                .clamp(from.min(to), from.max(to));
        }
        let (_, phi) = piece_sum((from, x), root, coefficients, constants)?;
        end = End::Band;
        mino = polar;
        phi_radial = if k == 1 { phis[0] } else { 0.0 } + phi;
        u_end = match root {
            Some((u1, _)) => u1 - x * x,
            None => x,
        };
        outgoing_end = outgoing[k];
    }
    // The Kerr–Schild shift ∫ a dr / Δ from the start to the end, signed.
    let (mid, half) = (
        (0.5 * (u_start + u_end)) as f32,
        (0.5 * (u_start - u_end)) as f32,
    );
    let mut ks_shift = 0.0_f32;
    for (node, weight) in GL_NODES.iter().zip(GL_WEIGHTS) {
        for side in [-1.0_f32, 1.0] {
            let u = mid + side * half * *node as f32;
            ks_shift += weight as f32 * a as f32 / (1.0 - 2.0 * u + (a2 as f32) * u * u);
        }
    }
    let ks_shift = f64::from(ks_shift * half);

    // Polar motion over Mino time `mino`, as a unit vector n = (sin θ cos ψ, sin θ sin ψ,
    // cos θ) with ψ the polar part of the azimuth, dψ/dτ = L / (|E| sin²θ). It moves on
    // the sphere under the potential -a² n_z² / 2; with |n'|² from energy conservation,
    // n'' = -ω² n + F(n), F = a² (n_z ẑ - (2 n_z² - n_z0²) n), ω = |n'(0)|. The great
    // circle n = A cos ωτ + B sin ωτ / ω is exact for a = 0; RK4 integrates the small
    // corrections to A and B, A' = -F sin ωτ / ω and B' = F cos ωτ, in binary32.
    let n0 = [sin, 0.0, cos];
    let dn0 = [cos * theta_rate, angular / (e_abs * sin), -sin * theta_rate];
    let omega = (dn0[0] * dn0[0] + dn0[1] * dn0[1] + dn0[2] * dn0[2])
        .sqrt()
        .max(1.0e-30);
    let h = mino / POLAR_STEPS as f64;
    // cos and sin / ω of the half-step phase advance the stage phases.
    let (step_s, step_c) = sin_cos(0.5 * omega * h);
    let (step_c, step_s) = (step_c as f32, (step_s / omega) as f32);
    let (omega2, a2_32, nz0_2) = ((omega * omega) as f32, a2 as f32, (cos * cos) as f32);
    let (n0_32, dn0_32) = (n0.map(|v| v as f32), dn0.map(|v| v as f32));
    let advance = |(c, s): (f32, f32)| (c * step_c - omega2 * s * step_s, s * step_c + c * step_s);
    let rates = |da: [f32; 3], db: [f32; 3], (c, s): (f32, f32)| {
        let n: [f32; 3] = std::array::from_fn(|i| (n0_32[i] + da[i]) * c + (dn0_32[i] + db[i]) * s);
        let k = a2_32 * (2.0 * n[2] * n[2] - nz0_2);
        let force = [-k * n[0], -k * n[1], a2_32 * n[2] - k * n[2]];
        (force.map(|v| -v * s), force.map(|v| v * c))
    };
    let h32 = h as f32;
    let (mut da, mut db) = ([0.0_f32; 3], [0.0_f32; 3]);
    let mut phase = (1.0_f32, 0.0_f32);
    for _ in 0..POLAR_STEPS {
        let middle = advance(phase);
        let end = advance(middle);
        let (ka1, kb1) = rates(da, db, phase);
        let (ka2, kb2) = rates(
            std::array::from_fn(|i| da[i] + 0.5 * h32 * ka1[i]),
            std::array::from_fn(|i| db[i] + 0.5 * h32 * kb1[i]),
            middle,
        );
        let (ka3, kb3) = rates(
            std::array::from_fn(|i| da[i] + 0.5 * h32 * ka2[i]),
            std::array::from_fn(|i| db[i] + 0.5 * h32 * kb2[i]),
            middle,
        );
        let (ka4, kb4) = rates(
            std::array::from_fn(|i| da[i] + h32 * ka3[i]),
            std::array::from_fn(|i| db[i] + h32 * kb3[i]),
            end,
        );
        for i in 0..3 {
            da[i] += h32 / 6.0 * (ka1[i] + 2.0 * ka2[i] + 2.0 * ka3[i] + ka4[i]);
            db[i] += h32 / 6.0 * (kb1[i] + 2.0 * kb2[i] + 2.0 * kb3[i] + kb4[i]);
        }
        phase = end;
    }
    let arc = omega * mino;
    let (big_s, big_c) = sin_cos(arc);
    let (s_end, w_s) = (big_s / omega, omega * big_s);
    let n: [f64; 3] = std::array::from_fn(|i| {
        (n0[i] + f64::from(da[i])) * big_c + (dn0[i] + f64::from(db[i])) * s_end
    });
    let dn: [f64; 3] = std::array::from_fn(|i| {
        -(n0[i] + f64::from(da[i])) * w_s + (dn0[i] + f64::from(db[i])) * big_c
    });
    let length = (n[0] * n[0] + n[1] * n[1] + n[2] * n[2]).sqrt();
    let c = n[2] / length;
    let rho = (n[0] * n[0] + n[1] * n[1]).sqrt();
    let sin = rho / length;
    // At the band, the polar sums and the RK4 motion must agree.
    if !(sin * sin > POLAR_FLOOR && (end != End::Band || (c.abs() - band).abs() < 1.0e-5)) {
        return None;
    }
    let sign_e = if energy < 0.0 { -1.0 } else { 1.0 };
    let (sd, cd) = sin_cos(sign_e * phi_radial + ks_shift);
    // Rotate by the radial azimuth, then by ψ.
    let (cp, sp) = (cp * cd - sp * sd, sp * cd + cp * sd);
    let (cpsi, spsi) = (n[0] / rho, n[1] / rho);
    let (cp, sp) = (cp * cpsi - sp * spsi, sp * cpsi + cp * spsi);

    // Rebuild the Cartesian state at radius 1 / u_end, as `super::rebuild`.
    let r = 1.0 / u_end;
    let v = dn[2] / length;
    let delta = r * r - 2.0 * r + a2;
    let radial = r * r * r * r * f(u_end).max(0.0);
    let p_theta = -e_abs * v / sin;
    let sign_r = if outgoing_end { 1.0 } else { -1.0 };
    let p_r = (sign_r * e_abs * radial.sqrt() + 2.0 * r * energy - a * angular) / delta;
    let big_x = (r * cp - a * sp) * sin;
    let big_y = (r * sp + a * cp) * sin;
    let big_z = r * c;
    let j = [
        [cp * sin, sp * sin, c],
        [(r * cp - a * sp) * c, (r * sp + a * cp) * c, -r * sin],
        [-(r * sp + a * cp) * sin, (r * cp - a * sp) * sin, 0.0],
    ];
    let rhs = [p_r, p_theta, angular];
    let det3 = |m: [[f64; 3]; 3]| {
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    };
    let inv_det = 1.0 / det3(j);
    let solve = |col: usize| {
        let mut m = j;
        for row in 0..3 {
            m[row][col] = rhs[row];
        }
        det3(m) * inv_det
    };
    let (p_x, p_y, p_z) = (solve(0), solve(1), solve(2));
    Some(Leg {
        position: [big_y, big_z, big_x],
        momentum: [-energy, p_y, p_z, p_x],
        end,
        outgoing: outgoing_end,
        arc,
    })
}

#[cfg(test)]
mod tests {
    use super::super::tests::{angle, camera_ray};
    use super::super::{Method, Outcome, direction, propagate, setup};
    use super::*;
    use proptest::prelude::*;

    /// Position gap and direction error of a leg against the binary64 reference, which
    /// only runs outward to a radius: forward from the start when the leg ends going
    /// out, otherwise backward from the end of the leg, which must come back to the
    /// start.
    fn leg_error(
        spin: f64,
        (pos, p): ([f64; 3], [f64; 4]),
        inner: f64,
        band: f64,
    ) -> Result<(Leg, f64, f64), String> {
        let leg = vacuum_leg(spin, pos, p, inner, 1600.0, band).ok_or("rejected")?;
        let flip = |p: [f64; 4]| p.map(|v| -v);
        let radius = |pos, p| {
            setup(spin, pos, p)
                .map(|st| st.s.r)
                .map_err(|e| format!("{e:?}"))
        };
        let (expected, start, momentum) = if leg.outgoing {
            let target = radius(leg.position, leg.momentum)?;
            (
                propagate(spin, pos, p, target, Method::Quadrature),
                leg.position,
                leg.momentum,
            )
        } else {
            let target = radius(pos, p)?;
            let back = propagate(
                spin,
                leg.position,
                flip(leg.momentum),
                target,
                Method::Quadrature,
            );
            (back, pos, flip(p))
        };
        match expected {
            Ok(Outcome::Arrived {
                position: x,
                momentum: px,
            }) => {
                let gap = (0..3).map(|i| (start[i] - x[i]).abs()).fold(0.0, f64::max);
                let turn = angle(direction(spin, start, momentum), direction(spin, x, px));
                Ok((leg, gap, turn))
            }
            other => Err(format!("reference {other:?}")),
        }
    }

    /// The band half-width in cos θ of a disk with H/R = `aspect`, emitting to 4H.
    fn band_of(aspect: f64) -> f64 {
        let k = 4.0 * aspect;
        k / (1.0 + k * k).sqrt()
    }

    /// A ray at `radius` with |cos θ| = band × `height` (capped below 1).
    fn band_ray(
        spin: f64,
        radius: f64,
        band: f64,
        (side, height, phi): (bool, f64, f64),
        aim: (f64, f64),
        backward: bool,
    ) -> ([f64; 3], [f64; 4]) {
        let cos = (band * height).min(0.999);
        let theta = if side { cos.acos() } else { (-cos).acos() };
        camera_ray(spin, radius, (theta, phi), aim, backward)
    }

    proptest! {
        #[test]
        fn sin_cos_matches_the_standard_library(x in -1.0e4f64..1.0e4) {
            let (s, c) = sin_cos(x);
            let (rs, rc) = x.sin_cos();
            prop_assert!((s - rs).abs() < 4.0e-16 * x.abs().max(1.0) && (c - rc).abs() < 4.0e-16 * x.abs().max(1.0));
        }

        #[test]
        fn outgoing_legs_match_the_separated_solution(
            spin in -0.99f64..0.99,
            radius in 13.0f64..800.0,
            at in (0.05f64..3.09, -3.1f64..3.1),
            (tilt, turn) in (0.0f64..1.55, -3.1f64..3.1),
            backward in any::<bool>(),
        ) {
            // Outward, tilted by up to 89 degrees from radial.
            let ray = camera_ray(spin, radius, at, (std::f64::consts::PI - tilt, turn), backward);
            match leg_error(spin, ray, 12.0, 0.0) {
                Ok((leg, gap, turn)) => {
                    prop_assert_eq!(leg.end, End::Sky);
                    prop_assert!(gap < 1.0e-6 * 1600.0 && turn < 1.0e-6, "gap {gap}, turn {turn}");
                }
                // The reference leaves vortical and near-polar rays unresolved.
                Err(e) if e.starts_with("reference Err") => {}
                Err(e) => prop_assert!(false, "{e}"),
            }
        }

        #[test]
        fn inward_legs_match_the_separated_solution(
            spin in -0.99f64..0.99,
            inner in 12.0f64..40.0,
            radius in 1.05f64..20.0,
            at in (0.05f64..3.09, -3.1f64..3.1),
            (tilt, turn) in (0.0f64..1.57, -3.1f64..3.1),
            backward in any::<bool>(),
        ) {
            // Inward, tilted by up to 90 degrees from radial: some turn outside the
            // sphere, the rest reach it.
            let ray = camera_ray(spin, inner * radius + 1.0, at, (tilt, turn), backward);
            match leg_error(spin, ray, inner, 0.0) {
                Ok((leg, gap, turn)) => {
                    let scale = if leg.end == End::Sky { 1600.0 } else { inner * radius };
                    prop_assert!(gap < 1.0e-6 * scale && turn < 1.0e-6, "{:?}, gap {gap}, turn {turn}", leg.end);
                }
                Err(e) if e.starts_with("reference Err") => {}
                Err(e) => prop_assert!(false, "{e}"),
            }
        }

        #[test]
        fn band_legs_match_the_separated_solution(
            spin in -0.99f64..0.99,
            radius in 12.5f64..60.0,
            aspect in 0.005f64..0.1,
            place in (any::<bool>(), 1.05f64..20.0, -3.1f64..3.1),
            aim in (0.0f64..3.1, -3.1f64..3.1),
            backward in any::<bool>(),
        ) {
            // Anywhere outside the band, in any direction.
            let band = band_of(aspect);
            let ray = band_ray(spin, radius, band, place, aim, backward);
            match leg_error(spin, ray, 12.0, band) {
                Ok((leg, gap, turn)) => {
                    let far = leg.position.iter().map(|x| x * x).sum::<f64>().sqrt();
                    let scale = far.max(radius);
                    prop_assert!(gap < 1.0e-6 * scale && turn < 1.0e-6, "{:?}, gap {gap}, turn {turn}", leg.end);
                }
                Err(e) if e.starts_with("reference Err") => {}
                Err(e) => prop_assert!(false, "{e}"),
            }
        }

        #[test]
        fn the_band_time_is_the_first_entry(
            spin in -0.99f64..0.99,
            radius in 12.5f64..60.0,
            aspect in 0.005f64..0.1,
            place in (any::<bool>(), 1.05f64..20.0, -3.1f64..3.1),
            aim in (0.0f64..3.1, -3.1f64..3.1),
        ) {
            // A binary64 RK4 march of the polar motion on the unit sphere, against the
            // first |cos θ| = band crossing from the quadrature.
            let band = band_of(aspect);
            let (pos, p) = band_ray(spin, radius, band, place, aim, false);
            let st = setup(spin, pos, p).unwrap();
            prop_assume!(st.eta > 0.0);
            let (s, a2, e_abs) = (st.s, spin * spin, st.k.energy.abs());
            let rate = -s.sin * s.p_theta / e_abs;
            let expected = band_time(s.cos, rate, band, (a2, st.lambda, st.eta)).unwrap();
            let mut n = [s.sin, 0.0, s.cos];
            let mut dn = [s.cos * s.p_theta / e_abs, st.k.angular / (e_abs * s.sin), rate];
            let accel = |n: [f64; 3], dn: [f64; 3]| {
                let speed2 = dn[0] * dn[0] + dn[1] * dn[1] + dn[2] * dn[2];
                let pull = a2 * n[2];
                let radial = speed2 + pull * n[2];
                [-radial * n[0], -radial * n[1], pull - radial * n[2]]
            };
            let h = expected / 4000.0;
            let mut crossed = None;
            for step in 0..4400 {
                let k1 = accel(n, dn);
                let n2: [f64; 3] = std::array::from_fn(|i| n[i] + 0.5 * h * dn[i]);
                let d2: [f64; 3] = std::array::from_fn(|i| dn[i] + 0.5 * h * k1[i]);
                let k2 = accel(n2, d2);
                let n3: [f64; 3] = std::array::from_fn(|i| n[i] + 0.5 * h * d2[i]);
                let d3: [f64; 3] = std::array::from_fn(|i| dn[i] + 0.5 * h * k2[i]);
                let k3 = accel(n3, d3);
                let n4: [f64; 3] = std::array::from_fn(|i| n[i] + h * d3[i]);
                let d4: [f64; 3] = std::array::from_fn(|i| dn[i] + h * k3[i]);
                let k4 = accel(n4, d4);
                let before = n[2].abs();
                for i in 0..3 {
                    n[i] += h / 6.0 * (dn[i] + 2.0 * d2[i] + 2.0 * d3[i] + d4[i]);
                    dn[i] += h / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]);
                }
                let after = n[2].abs();
                if after <= band {
                    // Linear interpolation inside the step.
                    crossed = Some((step as f64 + (before - band) / (before - after)) * h);
                    break;
                }
            }
            let crossed = crossed.ok_or("no crossing within 10% past the quadrature time");
            prop_assert!(crossed.is_ok(), "{:?}", crossed);
            let crossed = crossed.unwrap();
            prop_assert!((crossed - expected).abs() < 1.0e-5 * expected, "march {crossed}, quadrature {expected}");
        }
    }

    /// Error distribution of the legs; run with `-- --ignored --nocapture`.
    #[test]
    #[ignore = "statistics; run on demand"]
    fn vacuum_leg_error_statistics() {
        use proptest::strategy::ValueTree;
        use proptest::test_runner::TestRunner;
        let mut runner = TestRunner::deterministic();
        for label in ["outgoing", "inward", "band"] {
            let mut turns: [Vec<f64>; 3] = Default::default();
            let (mut rejected, mut unresolved) = (0, 0);
            let strategy = (
                -0.99f64..0.99,
                (12.0f64..40.0, 1.05f64..20.0),
                (0.005f64..0.1, any::<bool>(), 1.05f64..20.0),
                (0.05f64..3.09, -3.1f64..3.1),
                (0.0f64..1.57, -3.1f64..3.1),
                any::<bool>(),
            );
            for _ in 0..20_000 {
                let (spin, (inner, radius), (aspect, side, height), at, (tilt, turn), backward) =
                    strategy.new_tree(&mut runner).unwrap().current();
                let (ray, inner, band) = match label {
                    "outgoing" => {
                        let aim = (std::f64::consts::PI - tilt, turn);
                        (
                            camera_ray(spin, inner * radius + 1.0, at, aim, backward),
                            inner,
                            0.0,
                        )
                    }
                    "inward" => (
                        camera_ray(spin, inner * radius + 1.0, at, (tilt, turn), backward),
                        inner,
                        0.0,
                    ),
                    _ => {
                        let band = band_of(aspect);
                        let r = 12.5 + 2.4 * (radius - 1.05) / 0.95;
                        let ray = band_ray(
                            spin,
                            r,
                            band,
                            (side, height, at.1),
                            (2.0 * tilt, turn),
                            backward,
                        );
                        (ray, 12.0, band)
                    }
                };
                match leg_error(spin, ray, inner, band) {
                    Ok((leg, _, turn)) => turns[leg.end as usize].push(turn),
                    Err(e) if e.starts_with("reference Err") => unresolved += 1,
                    Err(_) => rejected += 1,
                }
            }
            for (end, t) in ["sky", "inner sphere", "band"].iter().zip(&mut turns) {
                if t.is_empty() {
                    continue;
                }
                t.sort_by(f64::total_cmp);
                let q = |f: f64| t[((t.len() - 1) as f64 * f) as usize];
                println!(
                    "{label} to the {end}: {} rays, median {:.2e}, p99 {:.2e}, max {:.2e}",
                    t.len(),
                    q(0.5),
                    q(0.99),
                    q(1.0)
                );
            }
            println!("{label}: {rejected} rejected, {unresolved} unresolved by the reference");
        }
    }
}
