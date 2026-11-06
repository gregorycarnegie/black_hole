use super::{Kerr, State, Unresolved, interval::Interval as I};

#[derive(Clone, Copy, Debug)]
pub struct Observation {
    pub direction: [f32; 3],
    pub direction_error_radians: f64,
    pub redshift: f32,
    pub redshift_relative_error: f64,
    pub screen_norm_error: f64,
    pub transversality_error: f64,
}

impl Kerr {
    /// Bound an output direction, transported screen and redshift for a timelike fluid velocity.
    pub fn observe(&self, state: State, velocity: [f64; 3]) -> Result<Observation, Unresolved> {
        let s = state.enclosure();
        if !self.domain(s)
            || state.error.iter().any(|x| !x.is_finite() || *x < 0.0)
            || velocity.iter().any(|x| !x.is_finite())
        {
            return Err(Unresolved::InvalidInput);
        }
        let m = self.geometry([s[0], s[1], s[2]]);
        let p: [I; 4] = std::array::from_fn(|i| s[i + 3]);
        let screen: [I; 4] = std::array::from_fn(|i| s[i + 7]);
        let k: [I; 4] =
            std::array::from_fn(|i| (0..4).fold(I::ZERO, |sum, j| sum + m.inv[i][j] * p[j]));
        let dot = |a: [I; 4], b: [I; 4]| {
            (0..4).fold(I::ZERO, |sum, i| {
                sum + (0..4).fold(I::ZERO, |sum, j| sum + m.g[i][j] * a[i] * b[j])
            })
        };
        let screen_norm_error = (dot(screen, screen) - I::ONE).magnitude();
        let transversality_error = (0..4)
            .fold(I::ZERO, |sum, i| sum + p[i] * screen[i])
            .magnitude();
        let u: [I; 4] = std::array::from_fn(|i| {
            if i == 0 {
                I::ONE
            } else {
                I::point(velocity[i - 1])
            }
        });
        let unorm = (-dot(u, u)).sqrt();
        let u = u.map(|x| x / unorm);
        let energy = (0..4).fold(I::ZERO, |sum, i| sum + p[i] * u[i]);
        if !energy.valid() || energy.lo <= 0.0 {
            return Err(Unresolved::Arithmetic);
        }
        let redshift = I::ONE / energy;
        let redshift_mid = redshift.midpoint() as f32;
        let redshift_relative_error =
            (I::point((redshift - I::point(f64::from(redshift_mid))).magnitude()) / redshift).hi;
        let spatial = [k[1], k[2], k[3]];
        let length = I::sum_squares(spatial).sqrt();
        let direction_box = spatial.map(|x| x / length);
        let direction = direction_box.map(|x| x.midpoint() as f32);
        // The output vector is interpreted after exact Euclidean normalization.
        let output = direction.map(|x| I::point(f64::from(x)));
        let output_length = I::sum_squares(output).sqrt();
        let output = output.map(|x| x / output_length);
        let difference = std::array::from_fn::<_, 3, _>(|i| direction_box[i] - output[i]);
        let chord = I::sum_squares(difference).sqrt();
        let angle = I::point(2.0) * chord;
        if !redshift.valid()
            || !angle.valid()
            || direction_box.iter().any(|x| !x.valid())
            || !redshift_relative_error.is_finite()
        {
            return Err(Unresolved::Arithmetic);
        }
        if angle.hi > 1e-6
            || redshift_relative_error > 1e-6
            || screen_norm_error > 1e-6
            || transversality_error > 1e-6
        {
            return Err(Unresolved::AccuracyBudget);
        }
        Ok(Observation {
            direction,
            direction_error_radians: angle.hi,
            redshift: redshift_mid,
            redshift_relative_error,
            screen_norm_error,
            transversality_error,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn includes_output_rounding_and_the_exact_static_redshift() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        let initial = kerr
            .initialize([100.0, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0])
            .unwrap();
        let observation = kerr.observe(initial, [0.0; 3]).unwrap();
        assert_eq!(observation.direction, [1.0, 0.0, 0.0]);
        let expected = (0.98f64).sqrt() / initial.phase[3];
        assert!(
            (f64::from(observation.redshift) / expected - 1.0).abs()
                <= observation.redshift_relative_error
        );
        assert!(observation.screen_norm_error < 1e-10 && observation.transversality_error < 1e-10);
    }

    #[test]
    fn rejects_spacelike_fluid_and_excessive_screen_error() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        let mut initial = kerr
            .initialize([100.0, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0])
            .unwrap();
        assert!(kerr.observe(initial, [4.0, 0.0, 0.0]).is_err());
        initial.error[9] = 1e-4;
        assert!(matches!(
            kerr.observe(initial, [0.0; 3]),
            Err(Unresolved::AccuracyBudget)
        ));
    }
}
