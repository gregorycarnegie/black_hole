use std::f32::consts::TAU;

use bevy::{ecs::system::SystemParam, prelude::*};

use crate::{
    camera::OrbitalCamera,
    controller::{active_gamepad, axis, stick},
};

// Re-export so compute::pipeline can keep its existing `use crate::simulation::…` imports.
pub use black_hole::physics::{
    SCHWARZSCHILD_RADIUS, kerr_horizon_radius_rg as kerr_horizon_radius,
    kerr_isco_radius_rg as kerr_isco_radius,
};

/// Default dimensionless Kerr spin parameter a* = J/M². Positive = prograde.
pub const KERR_SPIN: f32 = 0.82;

/// Center-to-center separation of the binary black holes, in units of SCHWARZSCHILD_RADIUS.
pub const BINARY_SEPARATION_RS: f32 = 7.0;

/// Inner radius used for the circumbinary disk cavity, in units of SCHWARZSCHILD_RADIUS.
pub const BINARY_DISK_INNER_RS: f32 = 5.0;

pub const BINARY_SPIN_STEP: f32 = 0.05;
pub const BINARY_AXIS_STEP: f32 = 0.1;

const BINARY_ORBIT_PERIOD_SECONDS: f32 = 18.0;
const MAX_SPIN_MAGNITUDE: f32 = 0.999;
const GAMEPAD_AXIS_EDIT_SPEED: f32 = 0.8;

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
    /// Outer disk radius in units of SCHWARZSCHILD_RADIUS.
    pub r_outer_rs: f32,
    /// Geometry regime / preset.
    pub model: DiskModel,
    /// H/R for the thin disk component (all models).
    pub h_thin: f32,
    /// H/R for the hot / thick inner component (TruncHot, Slim).
    pub h_hot: f32,
    /// Truncation radius (TruncHot) or puff radius (Slim), in units of SCHWARZSCHILD_RADIUS.
    pub r_trunc_rs: f32,
    /// Outer disk tilt angle in degrees (Warped).
    pub tilt_deg: f32,
    /// Bardeen-Petterson alignment radius in units of SCHWARZSCHILD_RADIUS (Warped).
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
            .add_systems(FixedUpdate, gravity_system)
            .add_systems(
                Update,
                (
                    toggle_binary_black_holes,
                    toggle_gravity,
                    toggle_debug_bodies,
                    update_disk_config,
                    animate_binary_black_holes,
                )
                    .chain(),
            );
    }
}

#[derive(Clone, Debug)]
pub struct SimObject {
    /// Position and radius in r_g; mass in units of the total black-hole mass.
    pub position: Vec3,
    pub radius: f32,
    pub color: Vec4,
    pub mass: f32,
    /// Velocity in gravitational radii per simulation time unit (c = 1).
    pub velocity: Vec3,
    /// Dimensionless spin vector a*. Direction is the spin axis; length is clamped to < 1.
    pub spin: Vec3,
}

/// All simulated objects in the scene, including the black hole itself.
#[derive(Resource)]
pub struct SimObjects(pub Vec<SimObject>);

impl Default for SimObjects {
    fn default() -> Self {
        Self(scene_objects(
            KERR_SPIN,
            false,
            true,
            0.0,
            default_binary_spins(),
        ))
    }
}

fn black_hole_radius(spin_magnitude: f32, mass_fraction: f32) -> f32 {
    kerr_horizon_radius(spin_magnitude) * mass_fraction
}

fn clamped_spin_vector(spin: Vec3) -> Vec3 {
    let length = spin.length();
    if length > MAX_SPIN_MAGNITUDE {
        spin / length * MAX_SPIN_MAGNITUDE
    } else {
        spin
    }
}

fn black_hole_object(
    spin_vector: Vec3,
    mass_fraction: f32,
    position: Vec3,
    velocity: Vec3,
) -> SimObject {
    let spin = clamped_spin_vector(spin_vector);
    SimObject {
        position,
        radius: black_hole_radius(spin.length(), mass_fraction),
        color: Vec4::new(0., 0., 0., 1.),
        mass: mass_fraction,
        velocity,
        spin,
    }
}

fn single_black_hole(spin: f32) -> SimObject {
    black_hole_object(Vec3::Y * spin, 1.0, Vec3::ZERO, Vec3::ZERO)
}

fn binary_black_holes(spins: [BinarySpin; 2], phase: f32) -> [SimObject; 2] {
    let orbital_radius = 0.5 * BINARY_SEPARATION_RS * SCHWARZSCHILD_RADIUS;
    let angular_velocity = TAU / BINARY_ORBIT_PERIOD_SECONDS;
    let (sin_phase, cos_phase) = phase.sin_cos();
    let position = Vec3::new(cos_phase * orbital_radius, 0.0, sin_phase * orbital_radius);
    let velocity = Vec3::new(
        -sin_phase * orbital_radius * angular_velocity,
        0.0,
        cos_phase * orbital_radius * angular_velocity,
    );

    [
        black_hole_object(spins[0].vector(), 0.5, position, velocity),
        black_hole_object(spins[1].vector(), 0.5, -position, -velocity),
    ]
}

pub(crate) fn scene_objects(
    spin: f32,
    include_debug_bodies: bool,
    binary_enabled: bool,
    binary_phase: f32,
    binary_spins: [BinarySpin; 2],
) -> Vec<SimObject> {
    let mut objects = Vec::new();

    if include_debug_bodies {
        objects.extend([
            SimObject {
                position: Vec3::new(64.0, 0.0, 0.0),
                radius: 6.4,
                color: Vec4::new(1., 1., 0., 1.),
                mass: 2.33e-7,
                velocity: Vec3::ZERO,
                spin: Vec3::ZERO,
            },
            SimObject {
                position: Vec3::new(0.0, 0.0, 64.0),
                radius: 6.4,
                color: Vec4::new(1., 0., 0., 1.),
                mass: 2.33e-7,
                velocity: Vec3::ZERO,
                spin: Vec3::ZERO,
            },
        ]);
    }

    if binary_enabled {
        objects.extend(binary_black_holes(binary_spins, binary_phase));
    } else {
        objects.push(single_black_hole(spin));
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
#[derive(SystemParam)]
struct DiskInputParams<'w, 's> {
    keys: Res<'w, ButtonInput<KeyCode>>,
    time: Res<'w, Time>,
    gamepads: Query<'w, 's, &'static Gamepad>,
    disk: ResMut<'w, DiskConfig>,
    cam: ResMut<'w, OrbitalCamera>,
    objects: ResMut<'w, SimObjects>,
    debug: Res<'w, DebugBodiesEnabled>,
    binary: ResMut<'w, BinaryBlackHoles>,
}

fn update_disk_config(mut input: DiskInputParams) {
    let mut changed = false;
    let mut rebuild_scene = false;
    let mut selection_changed = false;
    let mut binary_spin_changed = false;
    let mut binary_axis_changed = false;

    let active_gamepad = active_gamepad(&input.gamepads);
    let gamepad_spin_down =
        active_gamepad.is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::DPadDown));
    let gamepad_spin_up =
        active_gamepad.is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::DPadUp));

    if input.keys.just_pressed(KeyCode::KeyQ) || gamepad_spin_down {
        if input.binary.enabled {
            input.binary.adjust_selected_magnitude(-BINARY_SPIN_STEP);
            binary_spin_changed = true;
        } else {
            input.disk.spin =
                (input.disk.spin - 0.05).clamp(-MAX_SPIN_MAGNITUDE, MAX_SPIN_MAGNITUDE);
        }
        changed = true;
        rebuild_scene = true;
    }
    if input.keys.just_pressed(KeyCode::KeyE) || gamepad_spin_up {
        if input.binary.enabled {
            input.binary.adjust_selected_magnitude(BINARY_SPIN_STEP);
            binary_spin_changed = true;
        } else {
            input.disk.spin =
                (input.disk.spin + 0.05).clamp(-MAX_SPIN_MAGNITUDE, MAX_SPIN_MAGNITUDE);
        }
        changed = true;
        rebuild_scene = true;
    }
    if input.binary.enabled {
        let gamepad_select_a =
            active_gamepad.is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::DPadLeft));
        let gamepad_select_b =
            active_gamepad.is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::DPadRight));
        if input.keys.just_pressed(KeyCode::Digit1) || gamepad_select_a {
            input.binary.selected = 0;
            selection_changed = true;
        }
        if input.keys.just_pressed(KeyCode::Digit2) || gamepad_select_b {
            input.binary.selected = 1;
            selection_changed = true;
        }

        if let Some(gamepad) = active_gamepad {
            let axis_xy = stick(gamepad.right_stick());
            let z_axis = axis(
                gamepad.get(GamepadButton::RightTrigger).unwrap_or(0.0)
                    - gamepad.get(GamepadButton::LeftTrigger).unwrap_or(0.0),
            );
            let axis_delta = Vec3::new(axis_xy.x, axis_xy.y, z_axis)
                * GAMEPAD_AXIS_EDIT_SPEED
                * input.time.delta_secs();
            if axis_delta != Vec3::ZERO {
                input.binary.adjust_selected_axis_component(0, axis_delta.x);
                input.binary.adjust_selected_axis_component(1, axis_delta.y);
                input.binary.adjust_selected_axis_component(2, axis_delta.z);
                changed = true;
                rebuild_scene = true;
                binary_axis_changed = true;
            }
        }
    }
    if input.keys.just_pressed(KeyCode::KeyZ) {
        input.disk.r_outer_rs = (input.disk.r_outer_rs - 1.0).max(4.0);
        changed = true;
    }
    if input.keys.just_pressed(KeyCode::KeyX) {
        input.disk.r_outer_rs = (input.disk.r_outer_rs + 1.0).min(30.0);
        changed = true;
    }
    if input.keys.just_pressed(KeyCode::KeyM) {
        let next = input.disk.model.next();
        let spin = input.disk.spin;
        *input.disk = DiskConfig::for_model(next, spin);
        info!("Disk model: {}", input.disk.model.name());
        changed = true;
    }

    if changed {
        if input.binary.enabled && binary_spin_changed {
            let spin = input.binary.selected_spin();
            info!(
                "Binary hole {} spin: |a*|={:.2}, axis=({:+.2}, {:+.2}, {:+.2})",
                input.binary.selected_label(),
                spin.magnitude,
                spin.axis.x,
                spin.axis.y,
                spin.axis.z
            );
        } else if !input.binary.enabled || !binary_axis_changed {
            info!(
                "Disk: spin={:.2}, r_outer={:.0} r_s, model={}",
                input.disk.spin,
                input.disk.r_outer_rs,
                input.disk.model.name()
            );
        }
        if rebuild_scene {
            input.objects.0 = scene_objects(
                input.disk.spin,
                input.debug.0,
                input.binary.enabled,
                input.binary.phase,
                input.binary.spins,
            );
        }
        // Trigger TAA reset so the accumulation buffer clears immediately.
        input.cam.is_moving = true;
    }

    if selection_changed {
        info!("Binary spin target: hole {}", input.binary.selected_label());
        input.cam.is_moving = true;
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
    pub selected: usize,
    pub spins: [BinarySpin; 2],
}

#[derive(Clone, Copy, Debug)]
pub struct BinarySpin {
    pub magnitude: f32,
    pub axis: Vec3,
}

impl BinarySpin {
    pub fn new(magnitude: f32, axis: Vec3) -> Self {
        let axis = if axis.length_squared() > 1.0e-6 {
            axis.normalize()
        } else {
            Vec3::Y
        };
        Self {
            magnitude: magnitude.clamp(0.0, MAX_SPIN_MAGNITUDE),
            axis,
        }
    }

    pub fn vector(&self) -> Vec3 {
        self.axis * self.magnitude
    }
}

pub fn default_binary_spins() -> [BinarySpin; 2] {
    [
        BinarySpin::new(KERR_SPIN, Vec3::Y),
        BinarySpin::new(KERR_SPIN, Vec3::Y),
    ]
}

impl BinaryBlackHoles {
    pub fn selected_label(&self) -> &'static str {
        if self.selected == 0 { "A" } else { "B" }
    }

    pub fn selected_spin(&self) -> BinarySpin {
        self.spins[self.selected.min(1)]
    }

    pub fn select_prev(&mut self) {
        self.selected = (self.selected + 1) % 2;
    }

    pub fn select_next(&mut self) {
        self.selected = (self.selected + 1) % 2;
    }

    pub fn adjust_selected_magnitude(&mut self, delta: f32) {
        let selected = self.selected.min(1);
        let spin = self.spins[selected];
        self.spins[selected] = BinarySpin::new(spin.magnitude + delta, spin.axis);
    }

    pub fn adjust_selected_axis_component(&mut self, component: usize, delta: f32) {
        let selected = self.selected.min(1);
        let spin = self.spins[selected];
        let mut axis = spin.axis;
        match component {
            0 => axis.x = (axis.x + delta).clamp(-1.0, 1.0),
            1 => axis.y = (axis.y + delta).clamp(-1.0, 1.0),
            2 => axis.z = (axis.z + delta).clamp(-1.0, 1.0),
            _ => return,
        }
        self.spins[selected] = BinarySpin::new(spin.magnitude, axis);
    }
}

impl Default for BinaryBlackHoles {
    fn default() -> Self {
        Self {
            enabled: true,
            phase: 0.0,
            selected: 0,
            spins: default_binary_spins(),
        }
    }
}

fn toggle_binary_black_holes(
    keys: Res<ButtonInput<KeyCode>>,
    gamepads: Query<&Gamepad>,
    mut binary: ResMut<BinaryBlackHoles>,
    debug: Res<DebugBodiesEnabled>,
    disk: Res<DiskConfig>,
    mut objects: ResMut<SimObjects>,
    mut cam: ResMut<OrbitalCamera>,
) {
    let gamepad_pressed_b =
        active_gamepad(&gamepads).is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::East));
    if keys.just_pressed(KeyCode::KeyN) || gamepad_pressed_b {
        binary.enabled = !binary.enabled;
        objects.0 = scene_objects(
            disk.spin,
            debug.0,
            binary.enabled,
            binary.phase,
            binary.spins,
        );
        cam.is_moving = true;
        info!(
            "Binary black holes: {}",
            if binary.enabled { "ON" } else { "OFF" }
        );
    }
}

fn toggle_gravity(
    keys: Res<ButtonInput<KeyCode>>,
    gamepads: Query<&Gamepad>,
    mut gravity: ResMut<GravityEnabled>,
) {
    let gamepad_pressed_select = active_gamepad(&gamepads)
        .is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::Select));
    if keys.just_pressed(KeyCode::KeyG) || gamepad_pressed_select {
        gravity.0 = !gravity.0;
        info!("Gravity: {}", if gravity.0 { "ON" } else { "OFF" });
    }
}

fn toggle_debug_bodies(
    keys: Res<ButtonInput<KeyCode>>,
    gamepads: Query<&Gamepad>,
    mut enabled: ResMut<DebugBodiesEnabled>,
    disk: Res<DiskConfig>,
    binary: Res<BinaryBlackHoles>,
    mut objects: ResMut<SimObjects>,
    mut cam: ResMut<OrbitalCamera>,
) {
    let gamepad_pressed_start =
        active_gamepad(&gamepads).is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::Start));
    if keys.just_pressed(KeyCode::KeyO) || gamepad_pressed_start {
        enabled.0 = !enabled.0;
        objects.0 = scene_objects(
            disk.spin,
            enabled.0,
            binary.enabled,
            binary.phase,
            binary.spins,
        );
        cam.is_moving = true;
        info!("Debug bodies: {}", if enabled.0 { "ON" } else { "OFF" });
    }
}

fn gravity_system(
    time: Res<Time<Fixed>>,
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
                // G = 1; cancel the receiving mass before evaluating acceleration.
                let acc = objects.0[j].mass / (dist * dist);
                *acc_i += diff.normalize() * acc;
            }
        }
    }

    for (i, obj) in objects.0.iter_mut().enumerate() {
        obj.velocity += accelerations[i] * time.delta_secs();
        obj.position += obj.velocity * time.delta_secs();
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
    objects.0 = scene_objects(disk.spin, debug.0, true, binary.phase, binary.spins);
    cam.is_moving = true;
}

#[cfg(test)]
mod tests {
    use super::*;
    use bevy::time::TimeUpdateStrategy;
    use std::time::Duration;

    #[test]
    fn gravity_uses_elapsed_time_and_is_independent_of_render_rate() {
        let simulate = |fps: u32, enabled: bool, binary: bool| {
            let mut app = App::new();
            app.add_plugins(MinimalPlugins)
                .init_resource::<ButtonInput<KeyCode>>()
                .init_resource::<OrbitalCamera>()
                .add_plugins(SimulationPlugin)
                .insert_resource(GravityEnabled(enabled))
                .insert_resource(DebugBodiesEnabled(true))
                .insert_resource(BinaryBlackHoles {
                    enabled: binary,
                    ..default()
                })
                .insert_resource(SimObjects(scene_objects(
                    KERR_SPIN,
                    true,
                    false,
                    0.0,
                    default_binary_spins(),
                )))
                .insert_resource(TimeUpdateStrategy::ManualDuration(Duration::ZERO));
            app.update();
            let mut elapsed = Duration::ZERO;
            for frame in 1..=fps * 4 {
                let next = Duration::from_secs_f64(frame as f64 / fps as f64);
                app.insert_resource(TimeUpdateStrategy::ManualDuration(next - elapsed));
                app.update();
                elapsed = next;
            }
            app.world().resource::<SimObjects>().0.clone()
        };
        let reference = simulate(60, true, false);
        assert!(reference[0].velocity.x < 0.0);
        assert!(reference[0].position.x < 64.0);
        for fps in [30, 120] {
            for (actual, expected) in simulate(fps, true, false).iter().zip(&reference) {
                assert!(actual.position.is_finite() && actual.velocity.is_finite());
                assert_eq!(actual.position, expected.position);
                assert_eq!(actual.velocity, expected.velocity);
            }
        }
        assert_eq!(simulate(60, false, false)[0].position.x, 64.0);
        assert_eq!(simulate(60, true, true)[0].position.x, 64.0);

        // A massless test particle still accelerates; one half-unit step at r=10.
        let mut source = single_black_hole(0.0);
        source.mass = 1.0;
        let mut tracer = source.clone();
        tracer.position = Vec3::X * 10.0;
        tracer.mass = 0.0;
        let mut app = App::new();
        let mut time = Time::<Fixed>::default();
        time.advance_by(Duration::from_secs_f32(0.5));
        app.insert_resource(time)
            .insert_resource(GravityEnabled(true))
            .insert_resource(BinaryBlackHoles {
                enabled: false,
                ..default()
            })
            .insert_resource(SimObjects(vec![source, tracer]))
            .add_systems(FixedUpdate, gravity_system);
        app.world_mut().run_schedule(FixedUpdate);
        let objects = app.world().resource::<SimObjects>();
        assert!((objects.0[1].velocity.x + 0.005).abs() < 1e-7);
        assert!((objects.0[1].position.x - 9.9975).abs() < 1e-6);
        assert_eq!(objects.0[0].velocity, Vec3::ZERO);
    }
}
