// Ellis metric and planar null rays: James et al., arXiv:1502.03809,
// Eqs. (1), (2), (13), (16). Shared verbatim by the host and CUDA compiler.

pub const THROAT_RADIUS: f32 = 4.0;
pub const DUST_SPEED: f32 = -0.5;
pub const DUST_GAMMA: f32 = 1.154_700_5;

/// Exact pressureless test-dust solution of ∂t(A n) + v ∂l(A n) = 0,
/// A = l²+a². The finite-mass Lorentzian pulse starts at l=2a, with width a.
#[inline(always)]
pub fn dust_density(l: f32, time: f32, throat: f32) -> f32 {
    let label = (l - DUST_SPEED * time - 2.0 * throat) / throat;
    let shape = 1.0 + label * label;
    throat * throat / ((l * l + throat * throat) * shape * shape)
}

/// Emitted photon energy for a backwards-traced ray with radial tangent p.
#[inline(always)]
pub fn dust_photon_energy(p: f32) -> f32 {
    DUST_GAMMA * (1.0 + DUST_SPEED * p)
}

/// State = [proper radial distance l, radial momentum p, orbital angle phi].
#[inline(always)]
pub fn rhs(state: [f32; 3], impact: f32, throat: f32) -> [f32; 3] {
    let r2 = state[0] * state[0] + throat * throat;
    [
        state[1],
        impact * impact * state[0] / (r2 * r2),
        impact / r2,
    ]
}

#[inline(always)]
pub fn rk4(state: [f32; 3], impact: f32, throat: f32, h: f32) -> [f32; 3] {
    let k1 = rhs(state, impact, throat);
    let mut next = state;
    for i in 0..3 {
        next[i] = state[i] + 0.5 * h * k1[i];
    }
    let k2 = rhs(next, impact, throat);
    for i in 0..3 {
        next[i] = state[i] + 0.5 * h * k2[i];
    }
    let k3 = rhs(next, impact, throat);
    for i in 0..3 {
        next[i] = state[i] + h * k3[i];
    }
    let k4 = rhs(next, impact, throat);
    for i in 0..3 {
        next[i] = state[i] + h * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]) / 6.0;
    }
    next
}

/// Trace to |l| >= 400 a on an outgoing leg. None means unresolved/invalid,
/// never a claimed horizon: the renderer displays these pixels in magenta.
#[inline(always)]
pub fn trace(
    l: f32,
    p: f32,
    impact: f32,
    throat: f32,
    max_steps: u32,
    observer_time: Option<f32>,
) -> Option<([f32; 3], u32, f32)> {
    if !l.is_finite()
        || !p.is_finite()
        || !impact.is_finite()
        || !throat.is_finite()
        || throat <= 0.0
        || impact < 0.0
        || observer_time.is_some_and(|time| !time.is_finite())
    {
        return None;
    }
    // shortcut: leave a 1e-5 relative critical band unresolved; use validated
    // integration before claiming classifications arbitrarily near b = a.
    if (impact - throat).abs() <= 1e-5 * throat {
        return None;
    }
    let mut state = [l, p, 0.0];
    let mut affine = 0.0;
    let mut intensity = 0.0;
    for step in 0..max_steps {
        let r2 = state[0] * state[0] + throat * throat;
        let constraint = state[1] * state[1] + impact * impact / r2;
        if !constraint.is_finite() || (constraint - 1.0).abs() > 1e-4 || !state[2].is_finite() {
            return None;
        }
        if state[0].abs() >= 400.0 * throat && state[0] * state[1] > 0.0 {
            return Some((state, step, intensity));
        }
        // Resolve the throat and angular winding; grow steps in the flat ends.
        let h = 0.025 * (state[0].abs() + throat);
        let next = rk4(state, impact, throat, h);
        if let Some(time) = observer_time {
            let middle = rk4(state, impact, throat, 0.5 * h);
            let energy = dust_photon_energy(middle[1]);
            // Optically thin, flat-spectrum transfer: dI_obs/dλ = H n / ν_em.
            // t decreases along the backward ray, with normalized observer energy 1.
            intensity += h * dust_density(middle[0], time - affine - 0.5 * h, throat) / energy;
            if energy <= 0.0 || !intensity.is_finite() {
                return None;
            }
        }
        affine += h;
        state = next;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn simpson(f: impl Fn(f64) -> f64, start: f64, end: f64) -> f64 {
        let n = 8192;
        let h = (end - start) / n as f64;
        let mut sum = f(start) + f(end);
        for i in 1..n {
            sum += if i % 2 == 0 { 2.0 } else { 4.0 } * f(start + i as f64 * h);
        }
        sum * h / 3.0
    }

    #[test]
    fn rays_match_independent_orbit_quadrature_on_both_sides_of_critical_impact() {
        let a = THROAT_RADIUS as f64;
        let l = 12.0_f64;
        for ratio in [0.0, 0.1, 0.9, 0.999, 1.001, 1.2, 2.0] {
            let b = a * ratio;
            let p = -(1.0 - b * b / (l * l + a * a)).sqrt();
            let (result, _, _) =
                trace(l as f32, p as f32, b as f32, a as f32, 10_000, None).unwrap();
            assert_eq!(result[0] < 0.0, b < a, "b/a={ratio}");
            let end = result[0].abs() as f64;
            let angle = if b < a {
                simpson(
                    |x| b / (a * a * x.cosh().powi(2) - b * b).sqrt(),
                    -(end / a).asinh(),
                    (l / a).asinh(),
                )
            } else {
                let turn = (b * b - a * a).sqrt();
                let integrand = |x: f64| b / (b * b + turn * turn * x.sinh().powi(2)).sqrt();
                simpson(
                    integrand,
                    0.0,
                    ((l * l - turn * turn).sqrt() / turn).asinh(),
                ) + simpson(
                    integrand,
                    0.0,
                    ((end * end - turn * turn).sqrt() / turn).asinh(),
                )
            };
            assert!(
                (result[2] as f64 - angle).abs() < 0.001,
                "b/a={ratio}, GPU-shared phi={}, reference={angle}",
                result[2]
            );
        }
    }

    #[test]
    fn radial_rays_cross_and_invalid_or_critical_rays_remain_unresolved() {
        assert!(trace(12.0, -1.0, 0.0, THROAT_RADIUS, 1000, None).unwrap().0[0] < 0.0);
        assert!(trace(-12.0, 1.0, 0.0, THROAT_RADIUS, 1000, None).unwrap().0[0] > 0.0);
        for (l, p, b, a, steps) in [
            (12.0, -1.0, 0.0, 4.0, 1),
            (12.0, -1.0, 0.0, 0.0, 1000),
            (12.0, 0.0, 0.0, 4.0, 1000),
            (0.0, 0.0, 4.0, 4.0, 1000),
            (f32::NAN, -1.0, 0.0, 4.0, 1000),
        ] {
            assert!(trace(l, p, b, a, steps, None).is_none());
        }
    }

    #[test]
    fn evolving_dust_conserves_particle_number_and_crosses_the_throat() {
        let a = THROAT_RADIUS as f64;
        let expected = a * a * a * std::f64::consts::PI / 2.0;
        for time in [0.0, 8.0, 16.0, 24.0, 32.0] {
            let mass = simpson(
                |l| (l * l + a * a) * dust_density(l as f32, time, a as f32) as f64,
                -512.0,
                512.0,
            );
            assert!(
                (mass - expected).abs() / expected < 2e-5,
                "time={time}, mass={mass}"
            );
            let center = 2.0 * THROAT_RADIUS + DUST_SPEED * time;
            let weighted = (center * center + THROAT_RADIUS * THROAT_RADIUS)
                * dust_density(center, time, THROAT_RADIUS);
            assert!((weighted - THROAT_RADIUS * THROAT_RADIUS).abs() < 1e-6);
        }
        assert_eq!(dust_density(0.0, 16.0, THROAT_RADIUS), 1.0);
        assert!(dust_density(-8.0, 32.0, THROAT_RADIUS) > dust_density(-8.0, 0.0, THROAT_RADIUS));
    }

    #[test]
    fn emitted_intensity_matches_an_independent_retarded_radial_integral() {
        for observer_time in [0.0, 16.0, 32.0] {
            let (ray, _, intensity) =
                trace(12.0, -1.0, 0.0, THROAT_RADIUS, 10_000, Some(observer_time)).unwrap();
            let length = (12.0 - ray[0]) as f64;
            let energy = (1.0_f64 + 0.5) / (1.0_f64 - 0.25).sqrt();
            let reference = simpson(
                |s| {
                    let l = 12.0 - s;
                    let time = observer_time as f64 - s;
                    let label = (l + 0.5 * time - 8.0) / 4.0;
                    16.0 / ((l * l + 16.0) * (1.0 + label * label).powi(2)) / energy
                },
                0.0,
                length,
            );
            assert!(
                (intensity as f64 - reference).abs() < 0.002,
                "t={observer_time}, intensity={intensity}, reference={reference}"
            );
        }
        assert_eq!(
            trace(12.0, -1.0, 0.0, THROAT_RADIUS, 10_000, None)
                .unwrap()
                .2,
            0.0
        );
        assert!(trace(12.0, -1.0, 0.0, THROAT_RADIUS, 10_000, Some(f32::NAN)).is_none());
        assert!((DUST_GAMMA as f64 - 1.0_f64 / (1.0_f64 - 0.25).sqrt()).abs() < 1e-7);
    }
}
