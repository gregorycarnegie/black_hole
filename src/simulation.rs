use std::f32::consts::TAU;

use bevy::prelude::*;

use crate::camera::OrbitalCamera;

// Re-export so compute::pipeline can keep its existing `use crate::simulation::…` imports.
pub use black_hole::physics::{SAGA_RS, kerr_horizon_radius, kerr_isco_radius};

pub const C: f64 = 299_792_458.0;
pub const G_CONST: f64 = 6.6743e-11;
pub const SAGA_MASS: f64 = 8.54e36;

/// Default dimensionless Kerr spin parameter a* = J/M². Positive = prograde.
pub const KERR_SPIN: f32 = 0.82;

/// Center-to-center separation of the binary black holes, in units of SAGA_RS.
pub const BINARY_SEPARATION_RS: f32 = 7.0;

/// Inner radius used for the circumbinary disk cavity, in units of SAGA_RS.
pub const BINARY_DISK_INNER_RS: f32 = 5.0;

const BINARY_ORBIT_PERIOD_SECONDS: f32 = 18.0;
const BLACK_HOLE_SHADOW_RADIUS_MULTIPLIER: f32 = 2.6;

/// Accretion-disk geometry regime, selectable at runtime with M.
#[derive(Clone, Debug, PartialEq, Default)]
pub enum DiskModel {
    /// Geometrically thin Novikov-Thorne / Shakura-Sunyaev disk (soft state).
    #[default]
    ThinNt = 0,
    /// Truncated thin outer disk + thick hot inner flow (hard state / ADAF).
    TruncatedHotFlow = 1,
    /// Slim / super-Eddington disk: puffed-up photosphere and funnel.
    SlimFunnel = 2,
    /// Warped / Bardeen-Petterson tilted thin disk.
    WarpedThin = 3,
}

impl DiskModel {
    pub fn as_u32(&self) -> u32 {
        match self {
            Self::ThinNt => 0,
            Self::TruncatedHotFlow => 1,
            Self::SlimFunnel => 2,
            Self::WarpedThin => 3,
        }
    }

    pub fn next(&self) -> Self {
        match self {
            Self::ThinNt => Self::TruncatedHotFlow,
            Self::TruncatedHotFlow => Self::SlimFunnel,
            Self::SlimFunnel => Self::WarpedThin,
            Self::WarpedThin => Self::ThinNt,
        }
    }

    pub fn prev(&self) -> Self {
        match self {
            Self::ThinNt => Self::WarpedThin,
            Self::TruncatedHotFlow => Self::ThinNt,
            Self::SlimFunnel => Self::TruncatedHotFlow,
            Self::WarpedThin => Self::SlimFunnel,
        }
    }

    pub fn short_name(&self) -> &'static str {
        match self {
            Self::ThinNt => "Thin NT",
            Self::TruncatedHotFlow => "Truncated",
            Self::SlimFunnel => "Slim Funnel",
            Self::WarpedThin => "Warped",
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Self::ThinNt => "Thin NT disk (soft state)",
            Self::TruncatedHotFlow => "Truncated thin + hot flow (hard state)",
            Self::SlimFunnel => "Slim / super-Eddington funnel",
            Self::WarpedThin => "Warped / tilted thin disk (Bardeen-Petterson)",
        }
    }
}

/// Runtime-adjustable accretion disk and black hole parameters.
#[derive(Resource, Clone, Debug)]
pub struct DiskConfig {
    /// Dimensionless Kerr spin parameter a* ∈ (−0.999, 0.999).
    pub spin: f32,
    /// Outer disk radius in units of SAGA_RS.
    pub r_outer_rs: f32,
    /// Geometry regime / preset.
    pub model: DiskModel,
    /// H/R for the thin disk component (all models).
    pub h_thin: f32,
    /// H/R for the hot / thick inner component (TruncHot, Slim).
    pub h_hot: f32,
    /// Truncation radius (TruncHot) or puff radius (Slim), in units of SAGA_RS.
    pub r_trunc_rs: f32,
    /// Outer disk tilt angle in degrees (Warped).
    pub tilt_deg: f32,
    /// Bardeen-Petterson alignment radius in units of SAGA_RS (Warped).
    pub r_bp_rs: f32,
    /// Azimuthal twist per ln(r/r_bp) in degrees (Warped).
    pub twist_deg: f32,
}

impl DiskConfig {
    /// Return a preset `DiskConfig` for the given model, preserving spin.
    pub fn for_model(model: DiskModel, spin: f32) -> Self {
        match model {
            DiskModel::ThinNt => Self {
                spin,
                r_outer_rs: 15.0,
                model: DiskModel::ThinNt,
                h_thin: 0.03,
                h_hot: 0.5,
                r_trunc_rs: 10.0,
                tilt_deg: 0.0,
                r_bp_rs: 5.0,
                twist_deg: 0.0,
            },
            DiskModel::TruncatedHotFlow => Self {
                spin,
                r_outer_rs: 20.0,
                model: DiskModel::TruncatedHotFlow,
                h_thin: 0.02,
                h_hot: 0.5,
                r_trunc_rs: 10.0,
                tilt_deg: 0.0,
                r_bp_rs: 5.0,
                twist_deg: 0.0,
            },
            DiskModel::SlimFunnel => Self {
                spin,
                r_outer_rs: 12.0,
                model: DiskModel::SlimFunnel,
                h_thin: 0.05,
                h_hot: 0.45,
                r_trunc_rs: 3.0,
                tilt_deg: 0.0,
                r_bp_rs: 5.0,
                twist_deg: 0.0,
            },
            DiskModel::WarpedThin => Self {
                spin,
                r_outer_rs: 15.0,
                model: DiskModel::WarpedThin,
                h_thin: 0.03,
                h_hot: 0.5,
                r_trunc_rs: 5.0,
                tilt_deg: 30.0,
                r_bp_rs: 3.0,
                twist_deg: 15.0,
            },
        }
    }
}

impl Default for DiskConfig {
    fn default() -> Self {
        Self::for_model(DiskModel::ThinNt, KERR_SPIN)
    }
}

pub struct SimulationPlugin;

impl Plugin for SimulationPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<SimObjects>()
            .init_resource::<GravityEnabled>()
            .init_resource::<DebugBodiesEnabled>()
            .init_resource::<BinaryBlackHoles>()
            .init_resource::<DiskConfig>()
            .add_systems(
                Update,
                (
                    toggle_binary_black_holes,
                    toggle_gravity,
                    toggle_debug_bodies,
                    update_disk_config,
                    gravity_system,
                    animate_binary_black_holes,
                )
                    .chain(),
            );
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
        Self(scene_objects(KERR_SPIN, false, true, 0.0))
    }
}

fn black_hole_shadow_radius(spin: f32, mass_fraction: f32) -> f32 {
    kerr_horizon_radius(spin) * mass_fraction * BLACK_HOLE_SHADOW_RADIUS_MULTIPLIER
}

fn black_hole_object(spin: f32, mass_fraction: f32, position: Vec3, velocity: Vec3) -> SimObject {
    SimObject {
        position,
        radius: black_hole_shadow_radius(spin, mass_fraction),
        color: Vec4::new(0., 0., 0., 1.),
        mass: SAGA_MASS as f32 * mass_fraction,
        velocity,
    }
}

fn binary_black_holes(spin: f32, phase: f32) -> [SimObject; 2] {
    let orbital_radius = 0.5 * BINARY_SEPARATION_RS * SAGA_RS;
    let angular_velocity = TAU / BINARY_ORBIT_PERIOD_SECONDS;
    let (sin_phase, cos_phase) = phase.sin_cos();
    let position = Vec3::new(cos_phase * orbital_radius, 0.0, sin_phase * orbital_radius);
    let velocity = Vec3::new(
        -sin_phase * orbital_radius * angular_velocity,
        0.0,
        cos_phase * orbital_radius * angular_velocity,
    );

    [
        black_hole_object(spin, 0.5, position, velocity),
        black_hole_object(spin, 0.5, -position, -velocity),
    ]
}

pub(crate) fn scene_objects(
    spin: f32,
    include_debug_bodies: bool,
    binary_enabled: bool,
    binary_phase: f32,
) -> Vec<SimObject> {
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

    if binary_enabled {
        objects.extend(binary_black_holes(spin, binary_phase));
    } else {
        objects.push(black_hole_object(spin, 1.0, Vec3::ZERO, Vec3::ZERO));
    }
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
/// | N   | Toggle binary black holes           |
fn update_disk_config(
    keys: Res<ButtonInput<KeyCode>>,
    mut disk: ResMut<DiskConfig>,
    mut cam: ResMut<OrbitalCamera>,
    mut objects: ResMut<SimObjects>,
    debug: Res<DebugBodiesEnabled>,
    binary: Res<BinaryBlackHoles>,
) {
    let mut changed = false;
    let mut rebuild_scene = false;

    if keys.just_pressed(KeyCode::KeyQ) {
        disk.spin = (disk.spin - 0.05).clamp(-0.999, 0.999);
        changed = true;
        rebuild_scene = true;
    }
    if keys.just_pressed(KeyCode::KeyE) {
        disk.spin = (disk.spin + 0.05).clamp(-0.999, 0.999);
        changed = true;
        rebuild_scene = true;
    }
    if keys.just_pressed(KeyCode::KeyZ) {
        disk.r_outer_rs = (disk.r_outer_rs - 1.0).max(4.0);
        changed = true;
    }
    if keys.just_pressed(KeyCode::KeyX) {
        disk.r_outer_rs = (disk.r_outer_rs + 1.0).min(30.0);
        changed = true;
    }
    if keys.just_pressed(KeyCode::KeyM) {
        let next = disk.model.next();
        *disk = DiskConfig::for_model(next, disk.spin);
        info!("Disk model: {}", disk.model.name());
        changed = true;
    }

    if changed {
        info!(
            "Disk: spin={:.2}, r_outer={:.0} r_s, model={}",
            disk.spin,
            disk.r_outer_rs,
            disk.model.name()
        );
        if rebuild_scene {
            objects.0 = scene_objects(disk.spin, debug.0, binary.enabled, binary.phase);
        }
        // Trigger TAA reset so the accumulation buffer clears immediately.
        cam.is_moving = true;
    }
}

#[derive(Resource, Default)]
pub struct GravityEnabled(pub bool);

#[derive(Resource, Default)]
pub struct DebugBodiesEnabled(pub bool);

#[derive(Resource, Clone, Debug)]
pub struct BinaryBlackHoles {
    pub enabled: bool,
    pub phase: f32,
}

impl Default for BinaryBlackHoles {
    fn default() -> Self {
        Self {
            enabled: true,
            phase: 0.0,
        }
    }
}

fn toggle_binary_black_holes(
    keys: Res<ButtonInput<KeyCode>>,
    mut binary: ResMut<BinaryBlackHoles>,
    debug: Res<DebugBodiesEnabled>,
    disk: Res<DiskConfig>,
    mut objects: ResMut<SimObjects>,
    mut cam: ResMut<OrbitalCamera>,
) {
    if keys.just_pressed(KeyCode::KeyN) {
        binary.enabled = !binary.enabled;
        objects.0 = scene_objects(disk.spin, debug.0, binary.enabled, binary.phase);
        cam.is_moving = true;
        info!(
            "Binary black holes: {}",
            if binary.enabled { "ON" } else { "OFF" }
        );
    }
}

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
    binary: Res<BinaryBlackHoles>,
    mut objects: ResMut<SimObjects>,
    mut cam: ResMut<OrbitalCamera>,
) {
    if keys.just_pressed(KeyCode::KeyO) {
        enabled.0 = !enabled.0;
        objects.0 = scene_objects(disk.spin, enabled.0, binary.enabled, binary.phase);
        cam.is_moving = true;
        info!("Debug bodies: {}", if enabled.0 { "ON" } else { "OFF" });
    }
}

fn gravity_system(
    mut objects: ResMut<SimObjects>,
    gravity: Res<GravityEnabled>,
    binary: Res<BinaryBlackHoles>,
) {
    if !gravity.0 || binary.enabled {
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

fn animate_binary_black_holes(
    time: Res<Time>,
    mut binary: ResMut<BinaryBlackHoles>,
    debug: Res<DebugBodiesEnabled>,
    disk: Res<DiskConfig>,
    mut objects: ResMut<SimObjects>,
    mut cam: ResMut<OrbitalCamera>,
) {
    if !binary.enabled {
        return;
    }

    binary.phase =
        (binary.phase + time.delta_secs() * TAU / BINARY_ORBIT_PERIOD_SECONDS).rem_euclid(TAU);
    objects.0 = scene_objects(disk.spin, debug.0, true, binary.phase);
    cam.is_moving = true;
}
