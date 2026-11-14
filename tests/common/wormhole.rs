use black_hole::{cuda::shared_cuda, ellis};

fn fixtures(text: &str) -> Vec<[f32; 7]> {
    text.lines()
        .map(|line| {
            let values: Vec<f32> = line
                .split(',')
                .map(|number| {
                    let (num, den) = number.split_once('/').unwrap();
                    num.parse::<f32>().unwrap() / den.parse::<f32>().unwrap()
                })
                .collect();
            values.try_into().unwrap()
        })
        .collect()
}

#[test]
fn wormhole_rhs_matches_lean_checked_fixtures() {
    let fixtures = fixtures(include_str!("../../verification/fixtures/ellis-rhs.csv"));
    assert_eq!(fixtures.len(), 8);
    for [l, p, b, a, dl, dp, dphi] in fixtures {
        let result = ellis::rhs([l, p, 0.0], b, a);
        for (actual, expected) in result.into_iter().zip([dl, dp, dphi]) {
            assert!((actual - expected).abs() < 1e-6 * expected.abs().max(1.0));
        }
    }
}

#[test]
#[ignore = "requires a CUDA GPU; tests the actual shared wormhole solver"]
fn wormhole_cuda_matches_lean_rhs_and_host_traces() {
    let cuda = shared_cuda();
    let fixtures = fixtures(include_str!("../../verification/fixtures/ellis-rhs.csv"));
    let mut inputs: Vec<[f32; 4]> = fixtures
        .iter()
        .map(|r| r[..4].try_into().unwrap())
        .collect();
    for ratio in [0.0, 0.1, 0.9, 0.999, 1.001, 1.2, 2.0] {
        let b = ellis::THROAT_RADIUS * ratio;
        let p = -(1.0 - b * b / 160.0).sqrt();
        inputs.push([12.0, p, b, ellis::THROAT_RADIUS]);
    }
    let results: Vec<[[f32; 4]; 2]> = cuda.run_1d(&cuda.test_wormhole, &inputs, 32);
    for (i, (&[l, p, b, a], result)) in inputs.iter().zip(&results).enumerate() {
        let expected = if i < fixtures.len() {
            fixtures[i][4..].try_into().unwrap()
        } else {
            ellis::rhs([l, p, 0.0], b, a)
        };
        for (actual, expected) in result[0][..3].iter().zip(expected) {
            assert!((actual - expected).abs() < 1e-6 * expected.abs().max(1.0));
        }
        match ellis::trace(l, p, b, a, 10_000, None) {
            None => assert_eq!(result[1][3], -1.0),
            Some((state, _, _)) => {
                assert!(result[1][3] > 0.0);
                assert_eq!(result[1][0] < 0.0, state[0] < 0.0);
                for (actual, expected) in result[1][..3].iter().zip(state) {
                    assert!(
                        (actual - expected).abs() < 2e-4 * expected.abs().max(1.0),
                        "case={i}: {actual} vs {expected}"
                    );
                }
            }
        }
    }
}

#[test]
fn dust_density_and_doppler_match_lean_checked_fixtures() {
    let cases = fixtures(include_str!("../../verification/fixtures/ellis-dust.csv"));
    assert_eq!(cases.len(), 8);
    for [l, t, p, a, n, weighted, energy_squared] in cases {
        let density = ellis::dust_density(l, t, a);
        let energy = ellis::dust_photon_energy(p);
        for (actual, expected) in [density, (l * l + a * a) * density, energy * energy]
            .into_iter()
            .zip([n, weighted, energy_squared])
        {
            assert!((actual - expected).abs() < 1e-6 * expected.abs().max(1.0));
        }
    }
}

#[test]
#[ignore = "requires a CUDA GPU; checks density, Doppler energy and retarded transfer"]
fn dust_cuda_matches_lean_fixtures_and_host_intensity() {
    let cases = fixtures(include_str!("../../verification/fixtures/ellis-dust.csv"));
    let inputs: Vec<[f32; 4]> = cases.iter().map(|r| r[..4].try_into().unwrap()).collect();
    let cuda = shared_cuda();
    let results: Vec<[[f32; 4]; 2]> = cuda.run_1d(&cuda.test_dust, &inputs, 32);
    for (case, result) in cases.iter().zip(results) {
        for (actual, expected) in result[0][..3].iter().zip(&case[4..]) {
            assert!((actual - expected).abs() < 1e-6 * expected.abs().max(1.0));
        }
        match ellis::trace(case[0], case[2], 0.0, case[3], 10_000, Some(case[1])) {
            Some((state, _, intensity)) => {
                assert!(result[1][3] >= 0.0);
                assert_eq!(result[1][0] < 0.0, state[0] < 0.0);
                assert!((result[1][3] - intensity).abs() < 2e-4 * intensity.max(1.0));
            }
            None => assert_eq!(result[1][3], -1.0),
        }
    }
}
