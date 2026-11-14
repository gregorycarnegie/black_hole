//! Constant-Kruskal-time equatorial embeddings, G = c = M = 1 (r_s = 2).
//! Collas & Klein, arXiv:1107.4871, Eqs. (3), (5), (21), (22), (24).
//! This is a spatial embedding, not a traversable optical wormhole.

pub const MAX_TIME: f64 = 0.95;
const RS: f64 = 2.0;
const SEGMENTS: usize = 128;

// Monotone inversion of (R - 1) exp(R) = u² - v², where R = r/r_s.
// The private caller uses 0 <= u <= 32, |v| <= 0.95; [0, 8] brackets every root.
fn radius_ratio(u: f64, time: f64) -> f64 {
    let target = u * u - time * time;
    let (mut lo, mut hi) = (0.0, 8.0);
    for _ in 0..56 {
        let mid: f64 = (lo + hi) * 0.5;
        if (mid - 1.0) * mid.exp() < target {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    (lo + hi) * 0.5
}

fn height_derivative(ratio: f64, time: f64) -> f64 {
    let exponential = ratio.exp();
    2.0 * RS * (exponential - time * time).sqrt() / (ratio * exponential)
}

/// Positive half of the profile as [areal radius, embedding height], in r_g.
/// Reflect height to obtain the other exterior. Returns None outside the finite
/// display domain; the singular slices |v| = 1 are deliberately excluded.
pub fn profile(time: f64) -> Option<Vec<[f64; 2]>> {
    if !time.is_finite() || time.abs() > MAX_TIME {
        return None;
    }
    Some(sample_profile(time, SEGMENTS))
}

fn sample_profile(time: f64, segments: usize) -> Vec<[f64; 2]> {
    let mut points = Vec::with_capacity(segments + 1);
    let mut previous_u = 0.0;
    let mut ratio = radius_ratio(0.0, time);
    let mut previous_slope = height_derivative(ratio, time);
    let mut height = 0.0;
    points.push([RS * ratio, height]);
    for i in 1..=segments {
        // Resolve the narrow throat while retaining both asymptotically flat ends.
        let u = 32.0 * (i as f64 / segments as f64).powi(2);
        ratio = radius_ratio(u, time);
        let slope = height_derivative(ratio, time);
        let midpoint_slope = height_derivative(radius_ratio((previous_u + u) * 0.5, time), time);
        // shortcut: fixed Simpson quadrature, add error-controlled integration for precision exports.
        height += (u - previous_u) * (previous_slope + 4.0 * midpoint_slope + slope) / 6.0;
        points.push([RS * ratio, height]);
        previous_u = u;
        previous_slope = slope;
    }
    points
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn supported_slices_satisfy_kruskal_and_embedding_metrics() {
        for time in [-MAX_TIME, -0.75, 0.0, 0.75, MAX_TIME] {
            let points = profile(time).unwrap();
            assert_eq!(points, profile(-time).unwrap());
            for i in 0..=SEGMENTS {
                let u = 32.0 * (i as f64 / SEGMENTS as f64).powi(2);
                let ratio = points[i][0] / RS;
                let exponential = ratio.exp();
                let target = u * u - time * time;
                assert!(((ratio - 1.0) * exponential - target).abs() < 2e-12);
                let dr = 2.0 * RS * u / (ratio * exponential);
                let dz = height_derivative(ratio, time);
                let metric = 4.0 * RS * RS / (ratio * exponential);
                assert!((dr * dr + dz * dz - metric).abs() < 2e-12);
                assert!(points[i].iter().all(|x| x.is_finite()));
                if i > 0 {
                    assert!(points[i][0] > points[i - 1][0]);
                    assert!(points[i][1] > points[i - 1][1]);
                }
            }
            let refined = sample_profile(time, SEGMENTS * 4);
            for (i, point) in points.iter().enumerate() {
                assert!((point[1] - refined[i * 4][1]).abs() < 2e-5);
            }
        }
    }

    #[test]
    fn time_zero_is_the_two_sheet_flamm_paraboloid_and_throat_contracts() {
        let points = profile(0.0).unwrap();
        assert!((points[0][0] - RS).abs() < 1e-14);
        for [radius, height] in points {
            let exact_height = 2.0 * (RS * (radius - RS).max(0.0)).sqrt();
            assert!((height - exact_height).abs() < 2e-5);
        }
        let mut previous = RS;
        for i in 1..=95 {
            let throat = profile(i as f64 / 100.0).unwrap()[0][0];
            assert!(0.0 < throat && throat < previous);
            previous = throat;
        }
    }

    #[test]
    fn rejects_singular_and_nonfinite_slices() {
        for time in [1.0, -1.0, f64::NAN, f64::INFINITY, -f64::INFINITY] {
            assert!(profile(time).is_none());
        }
    }
}
