use super::*;
use proptest::prelude::*;

/// A null ray from `pos` with spatial covariant momentum `spatial`, and p_t > 0 (the
/// renderer's backward rays, E < 0) when `backward`.
fn null_ray(spin: f64, pos: [f64; 3], spatial: [f64; 3], backward: bool) -> [f64; 4] {
    let kerr = Kerr {
        spin: [0.0, spin, 0.0],
    };
    let inv = kerr.geometry::<f64>(pos).inv;
    let a = inv[0][0];
    let b = 2.0 * (0..3).map(|i| inv[0][i + 1] * spatial[i]).sum::<f64>();
    let c: f64 = (0..3)
        .flat_map(|i| (0..3).map(move |j| (i, j)))
        .map(|(i, j)| inv[i + 1][j + 1] * spatial[i] * spatial[j])
        .sum();
    let root = (b * b - 4.0 * a * c).sqrt();
    let candidates = [(-b + root) / (2.0 * a), (-b - root) / (2.0 * a)];
    let p_t = if backward {
        candidates[0].max(candidates[1])
    } else {
        candidates[0].min(candidates[1])
    };
    [p_t, spatial[0], spatial[1], spatial[2]]
}

/// A camera-like ray: position at `radius` in direction (θ, φ), momentum aimed at the
/// hole and turned by `offset` radians about a random axis.
pub(super) fn camera_ray(
    spin: f64,
    radius: f64,
    (theta, phi): (f64, f64),
    (offset, turn): (f64, f64),
    backward: bool,
) -> ([f64; 3], [f64; 4]) {
    let n = [
        theta.sin() * phi.cos(),
        theta.cos(),
        theta.sin() * phi.sin(),
    ];
    let pos = n.map(|v| radius * v);
    // An orthonormal pair perpendicular to n.
    let helper = if n[1].abs() < 0.9 {
        [0.0, 1.0, 0.0]
    } else {
        [1.0, 0.0, 0.0]
    };
    let cross = |u: [f64; 3], v: [f64; 3]| {
        [
            u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0],
        ]
    };
    let normalize = |u: [f64; 3]| {
        let l = (u[0] * u[0] + u[1] * u[1] + u[2] * u[2]).sqrt();
        u.map(|v| v / l)
    };
    let e1 = normalize(cross(n, helper));
    let e2 = cross(n, e1);
    let (so, co) = offset.sin_cos();
    let (st, ct) = turn.sin_cos();
    // Inward along -n, tilted by `offset` towards e1 cos(turn) + e2 sin(turn).
    let dir: [f64; 3] = std::array::from_fn(|i| -co * n[i] + so * (ct * e1[i] + st * e2[i]));
    // Spatial momentum along the travel direction, as the renderer's `init_ray`; the
    // sign of p_t picks forward or backward in time.
    let p = null_ray(spin, pos, dir, backward);
    (pos, p)
}

/// RK4 on the Cartesian Kerr–Schild geodesic until capture or Kerr–Schild radius 1600.
fn integrate(spin: f64, pos: [f64; 3], p: [f64; 4]) -> Option<[f64; 11]> {
    let kerr = Kerr {
        spin: [0.0, spin, 0.0],
    };
    let horizon = 1.0 + (1.0 - spin * spin).sqrt();
    let mut s = [0.0; 11];
    s[..3].copy_from_slice(&pos);
    s[3..7].copy_from_slice(&p);
    let add = |s: [f64; 11], d: [f64; 11], h: f64| std::array::from_fn(|i| s[i] + h * d[i]);
    for _ in 0..20_000_000 {
        let r = kerr.radius([s[0], s[1], s[2]]);
        if r > 1600.0 {
            return Some(s);
        }
        if r - horizon < 1.0e-4 {
            return None;
        }
        let k1 = kerr.phase_rhs(s);
        let speed = k1[..3].iter().map(|x| x * x).sum::<f64>().sqrt();
        let h = 0.002 * (r - horizon).min(r) / speed;
        let k2 = kerr.phase_rhs(add(s, k1, 0.5 * h));
        let k3 = kerr.phase_rhs(add(s, k2, 0.5 * h));
        let k4 = kerr.phase_rhs(add(s, k3, h));
        s = std::array::from_fn(|i| s[i] + h / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]));
    }
    None
}

pub(super) fn angle(u: [f64; 3], v: [f64; 3]) -> f64 {
    let dot: f64 = (0..3).map(|i| u[i] * v[i]).sum();
    let cross = [
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    ];
    (cross.iter().map(|x| x * x).sum::<f64>().sqrt()).atan2(dot)
}

fn rays() -> impl Strategy<Value = (f64, f64, (f64, f64), (f64, f64), bool)> {
    (
        -0.99f64..0.99,
        6.0f64..40.0,
        (0.2f64..2.94, -3.1f64..3.1),
        (0.0f64..0.6, -3.1f64..3.1),
        any::<bool>(),
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn the_radial_potential_matches_the_boyer_lindquist_momentum(
        (spin, radius, at, aim, backward) in rays()
    ) {
        let (pos, p) = camera_ray(spin, radius, at, aim, backward);
        let st = setup(spin, pos, p).unwrap();
        let s = st.s;
        let delta = s.r * s.r - 2.0 * s.r + spin * spin;
        let p_r_bl = s.p_r - (2.0 * s.r * st.k.energy - spin * st.k.angular) / delta;
        let (value, _) = Quartic::new(spin, st.lambda, st.eta).eval(Complex::real(s.r));
        let lhs = (p_r_bl * delta).powi(2);
        let rhs = st.k.energy.powi(2) * value.re;
        prop_assert!((lhs - rhs).abs() <= 1.0e-9 * lhs.abs().max(rhs.abs()), "{lhs} against {rhs}");
    }

    #[test]
    fn the_two_methods_agree((spin, radius, at, aim, backward) in rays()) {
        let (pos, p) = camera_ray(spin, radius, at, aim, backward);
        let elliptic = propagate(spin, pos, p, 1600.0, Method::Elliptic);
        let quadrature = propagate(spin, pos, p, 1600.0, Method::Quadrature);
        match (elliptic, quadrature) {
            (Ok(Outcome::Arrived { position: a, momentum: pa }),
             Ok(Outcome::Arrived { position: b, momentum: pb })) => {
                let gap = (0..3).map(|i| (a[i] - b[i]).abs()).fold(0.0, f64::max);
                prop_assert!(gap < 1.0e-8 * 1600.0, "positions {a:?} {b:?}");
                let turn = angle(direction(spin, a, pa), direction(spin, b, pb));
                prop_assert!(turn < 1.0e-9, "directions differ by {turn}");
            }
            (Err(Unresolved::Unsupported), _) => {}
            (a, b) => prop_assert_eq!(a, b),
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn the_separated_solution_matches_the_geodesic_equation(
        (spin, radius, at, aim, backward) in rays()
    ) {
        let (pos, p) = camera_ray(spin, radius, at, aim, backward);
        let start = constants(spin, pos, p);
        let numeric = integrate(spin, pos, p);
        let kerr = Kerr { spin: [0.0, spin, 0.0] };
        match numeric {
            None => {
                let analytic = propagate(spin, pos, p, 1600.0, Method::Quadrature);
                prop_assert!(
                    matches!(analytic, Ok(Outcome::Captured) | Err(Unresolved::Critical)),
                    "numeric capture, analytic {analytic:?}"
                );
            }
            Some(end) => {
                let x = [end[0], end[1], end[2]];
                let pe = [end[3], end[4], end[5], end[6]];
                let k = constants(spin, x, pe);
                let drift = (k.carter - start.carter).abs() / start.carter.abs().max(1.0);
                prop_assert!(drift < 1.0e-8, "Carter constant drifts by {drift}");
                prop_assert!((k.angular - start.angular).abs() < 1.0e-9 * start.angular.abs().max(1.0));
                let r = kerr.radius(x);
                for method in [Method::Elliptic, Method::Quadrature] {
                    match propagate(spin, pos, p, r, method) {
                        Ok(Outcome::Arrived { position, momentum }) => {
                            let gap = (0..3).map(|i| (position[i] - x[i]).abs()).fold(0.0, f64::max);
                            prop_assert!(gap < 1.0e-6 * r, "{method:?}: {position:?} against {x:?}");
                            let turn = angle(direction(spin, position, momentum), direction(spin, x, pe));
                            prop_assert!(turn < 1.0e-8, "{method:?}: directions differ by {turn}");
                        }
                        Err(Unresolved::Unsupported | Unresolved::Critical) => {}
                        other => prop_assert!(false, "{method:?}: numeric escape, analytic {other:?}"),
                    }
                }
            }
        }
    }
}

/// An image-like fan of rays from a camera near the equator and one near the pole,
/// including rays a millionth of a grid step from the meridional planes: every ray
/// must be resolved, identically classified by both methods, and arrive at the same
/// state.
#[test]
fn the_methods_agree_across_an_image_grid() {
    for spin in [0.0, 0.5, -0.9, 0.99] {
        for elevation in [1.47, 0.2] {
            let (mut arrived, mut captured) = (0, 0);
            for i in 0..24 {
                for j in 0..24 {
                    let offset = 0.02 + 0.5 * f64::from(i) / 24.0;
                    let turn = std::f64::consts::TAU * (f64::from(j) + 1.0e-6) / 24.0;
                    let (pos, p) = camera_ray(spin, 24.0, (elevation, 0.3), (offset, turn), true);
                    let elliptic = propagate(spin, pos, p, 1600.0, Method::Elliptic);
                    let quadrature = propagate(spin, pos, p, 1600.0, Method::Quadrature);
                    match (elliptic, quadrature) {
                        (
                            Ok(Outcome::Arrived {
                                position: a,
                                momentum: pa,
                            }),
                            Ok(Outcome::Arrived {
                                position: b,
                                momentum: pb,
                            }),
                        ) => {
                            let gap = (0..3).map(|k| (a[k] - b[k]).abs()).fold(0.0, f64::max);
                            let turn = angle(direction(spin, a, pa), direction(spin, b, pb));
                            assert!(
                                gap < 1.0e-8 * 1600.0 && turn < 1.0e-9,
                                "spin {spin} ({i}, {j}): {gap} {turn}"
                            );
                            arrived += 1;
                        }
                        (Ok(Outcome::Captured), Ok(Outcome::Captured)) => captured += 1,
                        other => panic!("spin {spin} elevation {elevation} ({i}, {j}): {other:?}"),
                    }
                }
            }
            assert!(
                arrived > 100 && captured > 100,
                "spin {spin}: {arrived} arrived, {captured} captured"
            );
        }
    }
}
