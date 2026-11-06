use super::{Kerr, State, Unresolved, interval::Interval as I};

impl Kerr {
    /// Past null ray with Eulerian energy one and a transverse unit screen.
    /// Inputs denote exact binary64 coordinates, a spatial direction and a screen hint.
    pub fn initialize(
        &self,
        position: [f64; 3],
        direction: [f64; 3],
        screen_hint: [f64; 3],
    ) -> Result<State, Unresolved> {
        if position
            .into_iter()
            .chain(direction)
            .chain(screen_hint)
            .any(|x| !x.is_finite())
        {
            return Err(Unresolved::InvalidInput);
        }
        let r2 = position
            .map(I::point)
            .into_iter()
            .fold(I::ZERO, |s, x| s + x.square());
        if !r2.valid() || r2.lo < 1.6 * 1.6 || r2.hi > 160.0 * 160.0 {
            return Err(Unresolved::OutsideDomain);
        }
        let m = self.geometry(position.map(I::point));
        let clearance = m.radius - self.horizon();
        if !clearance.valid() || clearance.lo < (I::ONE / I::point(500.0)).hi {
            return Err(Unresolved::OutsideDomain);
        }
        let spatial_dot = |a: [I; 3], b: [I; 3]| {
            (0..3).fold(I::ZERO, |s, i| {
                s + (0..3).fold(I::ZERO, |s, j| s + a[i] * m.g[i + 1][j + 1] * b[j])
            })
        };
        let d = direction.map(I::point);
        let dnorm = spatial_dot(d, d).sqrt();
        let d = d.map(|x| x / dnorm);
        let hint = screen_hint.map(I::point);
        let projection = spatial_dot(hint, d);
        let screen = std::array::from_fn(|i| hint[i] - projection * d[i]);
        let snorm = spatial_dot(screen, screen).sqrt();
        let screen = screen.map(|x| x / snorm);
        let alpha = I::ONE / (-m.inv[0][0]).sqrt();
        let tangent: [I; 4] = std::array::from_fn(|i| {
            if i == 0 {
                -I::ONE / alpha
            } else {
                alpha * m.inv[0][i] + d[i - 1]
            }
        });
        let momentum: [I; 4] =
            std::array::from_fn(|i| (0..4).fold(I::ZERO, |s, j| s + m.g[i][j] * tangent[j]));
        let enclosure: [I; 11] = std::array::from_fn(|i| {
            if i < 3 {
                I::point(position[i])
            } else if i < 7 {
                momentum[i - 3]
            } else if i == 7 {
                I::ZERO
            } else {
                screen[i - 8]
            }
        });
        if !self.domain(enclosure) {
            return Err(Unresolved::InvalidInput);
        }
        let phase = enclosure.map(I::midpoint);
        let error = std::array::from_fn(|i| (enclosure[i] - I::point(phase[i])).magnitude());
        Ok(State {
            phase,
            error,
            ticks: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initializes_null_unit_energy_and_transverse_screen_for_arbitrary_spin() {
        for spin in [[0.0; 3], [0.2, -0.7, 0.3]] {
            let kerr = Kerr::new(spin).unwrap();
            let initial = kerr
                .initialize([7.0, 3.0, -4.0], [-1.0, -0.2, 0.4], [0.0, 1.0, 0.0])
                .unwrap();
            let s = initial.enclosure();
            let m = kerr.geometry([s[0], s[1], s[2]]);
            let p: [I; 4] = std::array::from_fn(|i| s[i + 3]);
            let f: [I; 4] = std::array::from_fn(|i| s[i + 7]);
            let k: [I; 4] =
                std::array::from_fn(|i| (0..4).fold(I::ZERO, |s, j| s + m.inv[i][j] * p[j]));
            let dot = |a: [I; 4], b: [I; 4]| {
                (0..4).fold(I::ZERO, |s, i| {
                    s + (0..4).fold(I::ZERO, |s, j| s + m.g[i][j] * a[i] * b[j])
                })
            };
            let alpha = I::ONE / (-m.inv[0][0]).sqrt();
            let n = std::array::from_fn(|i| {
                if i == 0 {
                    I::ONE / alpha
                } else {
                    -alpha * m.inv[0][i]
                }
            });
            for (value, expected) in [
                (dot(k, k), 0.0),
                (dot(f, f), 1.0),
                (dot(k, f), 0.0),
                (dot(k, n), 1.0),
            ] {
                assert!(
                    value.valid() && value.lo <= expected && expected <= value.hi,
                    "{value:?} expected {expected}"
                );
                assert!(value.hi - value.lo < 1e-10);
            }
        }
    }

    #[test]
    fn rejects_degenerate_camera_data() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        for (position, direction, hint) in [
            ([4.0, 0.0, 0.0], [0.0; 3], [0.0, 1.0, 0.0]),
            ([4.0, 0.0, 0.0], [1.0, 0.0, 0.0], [1.0, 0.0, 0.0]),
            ([2.001, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0]),
            ([f64::NAN, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0]),
        ] {
            assert!(kerr.initialize(position, direction, hint).is_err());
        }
    }
}
