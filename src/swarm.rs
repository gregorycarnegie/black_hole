//! A swarm of small bodies on prescribed circular orbits: a stress test for
//! space-time acceleration structures. The renderer places each body where it
//! was when the light reaching the camera passed it, so inner bodies move
//! several gravitational radii during one photon's crossing of the belt.

use std::f64::consts::TAU;

use bevy::{prelude::*, render::extract_resource::ExtractResource};

use crate::camera::OrbitalCamera;

/// Body counts the K key and the panel cycle through.
pub(crate) const SWARM_COUNTS: [u32; 4] = [0, 256, 1024, 4096];
/// Coordinate time, in r_g/c, per real second.
const TIME_SCALE: f64 = 20.0;
/// Outside every Kerr ISCO (at most 9 r_g), so early capture stays valid, and
/// inside the 64 r_g far-field vacuum sphere.
const ORBIT_MIN: f32 = 12.0;
const ORBIT_MAX: f32 = 40.0;
const MAX_INCLINATION: f32 = 0.3;
const MAX_BODY_RADIUS: f32 = 0.5;

#[derive(Resource, Clone, Default, ExtractResource)]
#[extract_app(bevy::render::RenderApp)]
pub(crate) struct Swarm {
    pub count: u32,
    /// Coordinate time at the camera, in r_g/c.
    pub time: f64,
}

impl Swarm {
    pub(crate) fn step(&mut self, forward: bool) {
        let index = SWARM_COUNTS
            .iter()
            .position(|&count| count == self.count)
            .unwrap_or(0);
        let n = SWARM_COUNTS.len();
        self.count = SWARM_COUNTS[if forward {
            (index + 1) % n
        } else {
            (index + n - 1) % n
        }];
    }
}

/// Matches `SwarmBody` in `tools/cuda/kernels.rs`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, bytemuck::Pod, bytemuck::Zeroable)]
pub(crate) struct GpuSwarmBody {
    /// Orbital axis at phase 0, then orbit radius.
    pub axis_a: [f32; 4],
    /// Direction of motion at phase 0, then body radius.
    pub axis_b: [f32; 4],
    /// Phase at the camera time, angular velocity, albedo, unused.
    pub orbit: [f32; 4],
}

impl GpuSwarmBody {
    /// Centre at camera-relative coordinate time `t`.
    #[cfg(test)]
    pub(crate) fn center(&self, t: f64) -> [f64; 3] {
        let angle = f64::from(self.orbit[0]) + f64::from(self.orbit[1]) * t;
        let (sin, cos) = angle.sin_cos();
        let r = f64::from(self.axis_a[3]);
        std::array::from_fn(|k| {
            r * (cos * f64::from(self.axis_a[k]) + sin * f64::from(self.axis_b[k]))
        })
    }
}

pub struct SwarmPlugin;

impl Plugin for SwarmPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<Swarm>()
            .add_systems(Update, (cycle_swarm, advance_swarm).chain());
    }
}

fn cycle_swarm(keys: Res<ButtonInput<KeyCode>>, mut swarm: ResMut<Swarm>) {
    if keys.just_pressed(KeyCode::KeyK) {
        swarm.step(true);
        info!("Swarm bodies: {}", swarm.count);
    }
}

fn advance_swarm(time: Res<Time>, mut swarm: ResMut<Swarm>, mut cam: ResMut<OrbitalCamera>) {
    if swarm.count > 0 {
        swarm.time += time.delta_secs_f64() * TIME_SCALE;
        // The scene changes every frame, so temporal accumulation must restart.
        cam.is_moving = true;
    }
}

/// Deterministic uniform numbers in [0, 1) for body `index`.
fn unit_randoms<const N: usize>(index: u32) -> [f32; N] {
    std::array::from_fn(|k| {
        // splitmix64
        let mut z = (u64::from(index) << 8 | k as u64).wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        ((z ^ (z >> 31)) >> 40) as f32 / (1u64 << 24) as f32
    })
}

/// Bodies on a thick belt, prograde about +y, with phases at camera time `time`.
// shortcut: inclined orbits use the Kerr equatorial frequency and are not geodesics; switch to Kerr circular-orbit data if the physics matters.
pub(crate) fn swarm_bodies(count: u32, spin: f32, time: f64) -> Vec<GpuSwarmBody> {
    (0..count)
        .map(|index| {
            let [u_radius, u_node, u_tilt, u_phase, u_size, u_albedo] = unit_randoms(index);
            // Uniform per unit area across the belt.
            let r = (ORBIT_MIN * ORBIT_MIN
                + u_radius * (ORBIT_MAX * ORBIT_MAX - ORBIT_MIN * ORBIT_MIN))
                .sqrt();
            let node = std::f32::consts::TAU * u_node;
            let tilt = MAX_INCLINATION * (2.0 * u_tilt - 1.0);
            let (node_sin, node_cos) = node.sin_cos();
            let axis_a = Vec3::new(node_cos, 0.0, -node_sin);
            // Matches the disk's rotation sense, tangent (z, 0, -x).
            let axis_b = Vec3::new(-node_sin, 0.0, -node_cos) * tilt.cos() + Vec3::Y * tilt.sin();
            let omega = 1.0 / (f64::from(r).powf(1.5) + f64::from(spin));
            let phase = (TAU * f64::from(u_phase) + omega * time).rem_euclid(TAU);
            GpuSwarmBody {
                axis_a: axis_a.extend(r).into(),
                axis_b: axis_b
                    .extend(0.15 + (MAX_BODY_RADIUS - 0.15) * u_size * u_size)
                    .into(),
                orbit: [phase as f32, omega as f32, 0.35 + 0.65 * u_albedo, 0.0],
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use rstest::rstest;

    #[rstest]
    #[case::off_to_first(0, true, 256)]
    #[case::last_wraps_to_off(4096, true, 0)]
    #[case::off_back_to_last(0, false, 4096)]
    #[case::unknown_counts_as_off(7, true, 256)]
    fn counts_cycle_through_the_presets(
        #[case] start: u32,
        #[case] forward: bool,
        #[case] expected: u32,
    ) {
        let mut swarm = Swarm {
            count: start,
            time: 0.0,
        };
        swarm.step(forward);
        assert_eq!(swarm.count, expected);
    }

    #[test]
    fn k_cycles_and_an_active_swarm_resets_accumulation() {
        let mut app = App::new();
        app.add_plugins(MinimalPlugins)
            .init_resource::<ButtonInput<KeyCode>>()
            .init_resource::<OrbitalCamera>()
            .add_plugins(SwarmPlugin);
        app.update();
        assert!(!app.world().resource::<OrbitalCamera>().is_moving);
        app.world_mut()
            .resource_mut::<ButtonInput<KeyCode>>()
            .press(KeyCode::KeyK);
        app.update();
        assert_eq!(app.world().resource::<Swarm>().count, 256);
        assert!(app.world().resource::<OrbitalCamera>().is_moving);
    }

    #[test]
    fn bodies_are_deterministic() {
        let spin = 0.82;
        assert_eq!(swarm_bodies(64, spin, 3.0), swarm_bodies(64, spin, 3.0));
        assert_ne!(
            swarm_bodies(64, spin, 3.0)[0],
            swarm_bodies(64, spin, 3.0)[1]
        );
    }

    proptest! {
        #[test]
        fn bodies_stay_in_the_belt_on_prograde_orbits(index in 0u32..16384, time in 0.0..1.0e6_f64) {
            let spin = 0.82;
            let body = swarm_bodies(index + 1, spin, time)[index as usize];
            let a = Vec3::from_slice(&body.axis_a);
            let b = Vec3::from_slice(&body.axis_b);
            prop_assert!((a.length() - 1.0).abs() < 1e-5 && (b.length() - 1.0).abs() < 1e-5);
            prop_assert!(a.dot(b).abs() < 1e-5);
            // Angular momentum along +y, within the inclination limit.
            prop_assert!(a.cross(b).y >= MAX_INCLINATION.cos() - 1e-5);
            prop_assert!((ORBIT_MIN..=ORBIT_MAX).contains(&body.axis_a[3]));
            prop_assert!(body.axis_b[3] <= MAX_BODY_RADIUS && body.axis_a[3] - body.axis_b[3] > 9.0);
            prop_assert!((0.0..=std::f32::consts::TAU).contains(&body.orbit[0]));
        }

        #[test]
        fn camera_relative_time_matches_absolute_time(index in 0u32..1024, time in 0.0..1.0e5_f64, dt in -500.0..0.0_f64) {
            let spin = 0.82;
            let now = swarm_bodies(index + 1, spin, time)[index as usize];
            let earlier = swarm_bodies(index + 1, spin, time + dt)[index as usize];
            let [x, y, z] = now.center(dt);
            let [ex, ey, ez] = earlier.center(0.0);
            prop_assert!((x - ex).hypot(y - ey).hypot(z - ez) < 1e-3, "{:?} {:?}", now.center(dt), earlier.center(0.0));
        }
    }
}
