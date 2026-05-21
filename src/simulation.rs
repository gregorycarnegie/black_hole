use bevy::prelude::*;

use crate::camera::OrbitalCamera;

// Re-export so compute::pipeline can keep its existing `use crate::simulation::…` imports.
pub use black_hole::physics::{SAGA_RS, kerr_horizon_radius, kerr_isco_radius};

pub const C: f64 = 299_792_458.0;
pub const G_CONST: f64 = 6.6743e-11;
pub const SAGA_MASS: f64 = 8.54e36;

/// Default dimensionless Kerr spin parameter a* = J/M². Positive = prograde.
pub const KERR_SPIN: f32 = 0.82;

/// Runtime-adjustable accretion disk and black hole parameters.
#[derive(Resource, Clone, Debug)]
pub struct DiskConfig {
    /// Dimensionless Kerr spin parameter a* ∈ (−0.999, 0.999).
    pub spin: f32,
    /// Outer disk radius in units of SAGA_RS.
    pub r_outer_rs: f32,
}

impl Default for DiskConfig {
    fn default() -> Self {
        Self {
            spin: KERR_SPIN,
            r_outer_rs: 15.0,
        }
    }
}

pub struct SimulationPlugin;

impl Plugin for SimulationPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<SimObjects>()
            .init_resource::<GravityEnabled>()
            .init_resource::<DebugBodiesEnabled>()
            .init_resource::<DiskConfig>()
            .add_systems(Update, (toggle_gravity, gravity_system).chain())
            .add_systems(Update, (toggle_debug_bodies, update_disk_config).chain());
    }
}

#[derive(Clone, Debug)]
pub struct SimObject {
    pub position: Vec3,
    pub radius: f32,
    pub color: Vec4,
    pub mass: f32,
    pub velocity: Vec3,
}

/// All simulated objects in the scene, including the black hole itself.
#[derive(Resource)]
pub struct SimObjects(pub Vec<SimObject>);

impl Default for SimObjects {
    fn default() -> Self {
        Self(scene_objects(KERR_SPIN, false))
    }
}

fn black_hole_object(spin: f32) -> SimObject {
    SimObject {
        position: Vec3::ZERO,
        radius: kerr_horizon_radius(spin),
        color: Vec4::new(0., 0., 0., 1.),
        mass: SAGA_MASS as f32,
        velocity: Vec3::ZERO,
    }
}

fn scene_objects(spin: f32, include_debug_bodies: bool) -> Vec<SimObject> {
    let mut objects = Vec::new();

    if include_debug_bodies {
        objects.extend([
            SimObject {
                position: Vec3::new(4e11, 0.0, 0.0),
                radius: 4e10,
                color: Vec4::new(1., 1., 0., 1.),
                mass: 1.98892e30,
                velocity: Vec3::ZERO,
            },
            SimObject {
                position: Vec3::new(0.0, 0.0, 4e11),
                radius: 4e10,
                color: Vec4::new(1., 0., 0., 1.),
                mass: 1.98892e30,
                velocity: Vec3::ZERO,
            },
        ]);
    }

    // Keep the black hole last so systems can update its radius cheaply.
    objects.push(black_hole_object(spin));
    objects
}

/// Keyboard handler for runtime disk / BH parameter adjustment.
///
/// | Key | Action                              |
/// |-----|-------------------------------------|
/// | Q   | Decrease spin a* by 0.05            |
/// | E   | Increase spin a* by 0.05            |
/// | Z   | Decrease outer disk radius by 1 r_s |
/// | X   | Increase outer disk radius by 1 r_s |
/// | O   | Toggle debug orbiting bodies        |
fn update_disk_config(
    keys: Res<ButtonInput<KeyCode>>,
    mut disk: ResMut<DiskConfig>,
    mut cam: ResMut<OrbitalCamera>,
    mut objects: ResMut<SimObjects>,
) {
    let mut changed = false;

    if keys.just_pressed(KeyCode::KeyQ) {
        disk.spin = (disk.spin - 0.05).clamp(-0.999, 0.999);
        changed = true;
    }
    if keys.just_pressed(KeyCode::KeyE) {
        disk.spin = (disk.spin + 0.05).clamp(-0.999, 0.999);
        changed = true;
    }
    if keys.just_pressed(KeyCode::KeyZ) {
        disk.r_outer_rs = (disk.r_outer_rs - 1.0).max(4.0);
        changed = true;
    }
    if keys.just_pressed(KeyCode::KeyX) {
        disk.r_outer_rs = (disk.r_outer_rs + 1.0).min(30.0);
        changed = true;
    }

    if changed {
        info!(
            "Disk: spin={:.2}, r_outer={:.0} r_s",
            disk.spin, disk.r_outer_rs
        );
        // Keep the black hole sphere radius in sync with the new horizon.
        if let Some(bh) = objects.0.last_mut() {
            bh.radius = kerr_horizon_radius(disk.spin);
        }
        // Trigger TAA reset so the accumulation buffer clears immediately.
        cam.is_moving = true;
    }
}

#[derive(Resource, Default)]
pub struct GravityEnabled(pub bool);

#[derive(Resource, Default)]
pub struct DebugBodiesEnabled(pub bool);

fn toggle_gravity(keys: Res<ButtonInput<KeyCode>>, mut gravity: ResMut<GravityEnabled>) {
    if keys.just_pressed(KeyCode::KeyG) {
        gravity.0 = !gravity.0;
        info!("Gravity: {}", if gravity.0 { "ON" } else { "OFF" });
    }
}

fn toggle_debug_bodies(
    keys: Res<ButtonInput<KeyCode>>,
    mut enabled: ResMut<DebugBodiesEnabled>,
    disk: Res<DiskConfig>,
    mut objects: ResMut<SimObjects>,
    mut cam: ResMut<OrbitalCamera>,
) {
    if keys.just_pressed(KeyCode::KeyO) {
        enabled.0 = !enabled.0;
        objects.0 = scene_objects(disk.spin, enabled.0);
        cam.is_moving = true;
        info!("Debug bodies: {}", if enabled.0 { "ON" } else { "OFF" });
    }
}

fn gravity_system(mut objects: ResMut<SimObjects>, gravity: Res<GravityEnabled>) {
    if !gravity.0 {
        return;
    }

    let n = objects.0.len();
    let mut accelerations = vec![Vec3::ZERO; n];

    for (i, acc_i) in accelerations.iter_mut().enumerate() {
        for j in 0..n {
            if i == j {
                continue;
            }
            let diff = objects.0[j].position - objects.0[i].position;
            let dist = diff.length();
            if dist > 0.0 {
                let force =
                    (G_CONST as f32 * objects.0[i].mass * objects.0[j].mass) / (dist * dist);
                let acc = force / objects.0[i].mass;
                *acc_i += diff.normalize() * acc;
            }
        }
    }

    for (i, obj) in objects.0.iter_mut().enumerate() {
        obj.velocity += accelerations[i];
        obj.position += obj.velocity;
    }
}
