use bevy::{
    input::{
        InputSystems,
        mouse::{AccumulatedMouseMotion, AccumulatedMouseScroll},
    },
    prelude::*,
};
use std::f64::consts::PI;

use crate::controller::{active_gamepad, axis, stick};

pub struct OrbitalCameraPlugin;

pub const POLARIZATION_VIEWS: &[&str] = &["Intensity", "Linear %", "EVPA", "Q/I", "U/I", "V/I"];

const GAMEPAD_ORBIT_SPEED: f64 = 1.8;
const GAMEPAD_ZOOM_SPEED_MULTIPLIER: f64 = 8.0;

impl Plugin for OrbitalCameraPlugin {
    fn build(&self, app: &mut App) {
        // update_orbital_camera clears `is_moving` each frame, so it runs before every
        // Update system that sets it to request an accumulation reset.
        app.init_resource::<OrbitalCamera>()
            .add_systems(Startup, setup_cameras)
            .add_systems(PreUpdate, update_orbital_camera.after(InputSystems))
            .add_systems(
                Update,
                (toggle_heatmap, cycle_max_iter, sync_camera_transform),
            );
    }
}

/// Tracks the logical orbital camera state. Updated from mouse/keyboard input
/// each frame, then synced to the actual Bevy Camera3d transform.
///
/// Orbital parameters (`radius`, `azimuth`, `elevation`) are stored as `f64`
/// so that accumulated mouse/scroll input doesn't lose precision when the
/// camera is very close to the event horizon (~1 r_g). The GPU uniform is
/// still written as `f32` — the precision gain is on the CPU accumulation side.
#[derive(Resource)]
pub struct OrbitalCamera {
    pub radius: f64,
    pub azimuth: f64,
    pub elevation: f64,
    pub min_radius: f64,
    pub max_radius: f64,
    pub orbit_speed: f64,
    pub zoom_speed: f64,
    pub fov_degrees: f64,
    pub dragging: bool,
    pub is_moving: bool,
    /// When true the geodesic shader outputs an iteration-count heatmap instead
    /// of the normal render. Toggle with H.
    pub debug_heatmap: bool,
    /// Maximum geodesic integration steps per pixel. Press , / . to step through presets.
    pub max_iter: u32,
    pub polarization_view: u32,
    pub frequency_ghz: f32,
    pub faraday_depth: f32,
    pub conversion_depth: f32,
}

impl Default for OrbitalCamera {
    fn default() -> Self {
        Self {
            radius: 48.0,
            azimuth: 0.0,
            elevation: PI / 2.0 - 0.35,
            min_radius: 1.6,
            max_radius: 160.0,
            orbit_speed: 0.005,
            zoom_speed: 4.0,
            fov_degrees: 60.0,
            dragging: false,
            is_moving: false,
            debug_heatmap: false,
            max_iter: 10_000,
            polarization_view: 0,
            frequency_ghz: 230.0,
            faraday_depth: 1.0,
            conversion_depth: 0.3,
        }
    }
}

impl OrbitalCamera {
    /// Camera position in world space. Trig computed in f64; result cast to Vec3 (f32).
    pub fn position(&self) -> Vec3 {
        let elev = self.elevation.clamp(0.01, PI - 0.01);
        Vec3::new(
            (self.radius * elev.sin() * self.azimuth.cos()) as f32,
            (self.radius * elev.cos()) as f32,
            (self.radius * elev.sin() * self.azimuth.sin()) as f32,
        )
    }

    pub fn forward(&self) -> Vec3 {
        (Vec3::ZERO - self.position()).normalize()
    }

    pub fn right(&self) -> Vec3 {
        self.forward().cross(Vec3::Y).normalize()
    }

    pub fn up(&self) -> Vec3 {
        self.right().cross(self.forward())
    }

    pub fn tan_half_fov(&self) -> f32 {
        (self.fov_degrees.to_radians() * 0.5).tan() as f32
    }
}

/// Marker for the 3D perspective camera used to render the grid.
#[derive(Component)]
pub struct PerspectiveCamera;

/// Marker for the 2D camera used to display the compute-shader texture.
#[derive(Component)]
pub struct BackgroundCamera;

#[cfg_attr(test, mutants::skip)] // entity spawning only
fn setup_cameras(mut commands: Commands) {
    // 2D camera renders the compute-output sprite as a background (order 0).
    commands.spawn((
        Camera2d,
        Camera {
            order: 0,
            ..default()
        },
        BackgroundCamera,
    ));

    // 3D camera renders the spacetime grid on top (order 1, no color clear).
    commands.spawn((
        Camera3d::default(),
        Camera {
            order: 1,
            clear_color: ClearColorConfig::None,
            ..default()
        },
        PerspectiveCamera,
    ));
}

fn update_orbital_camera(
    mut cam: ResMut<OrbitalCamera>,
    mouse_button: Res<ButtonInput<MouseButton>>,
    mouse_motion: Res<AccumulatedMouseMotion>,
    scroll: Res<AccumulatedMouseScroll>,
    keys: Res<ButtonInput<KeyCode>>,
    time: Res<Time>,
    gamepads: Query<&Gamepad>,
) {
    cam.dragging = mouse_button.pressed(MouseButton::Left);
    cam.is_moving = false;

    if cam.dragging && mouse_motion.delta != Vec2::ZERO {
        // Cast f32 mouse deltas to f64 before accumulating to preserve precision.
        cam.azimuth += mouse_motion.delta.x as f64 * cam.orbit_speed;
        cam.elevation -= mouse_motion.delta.y as f64 * cam.orbit_speed;
        cam.elevation = cam.elevation.clamp(0.01, PI - 0.01);
        cam.is_moving = true;
    }

    if scroll.delta.y != 0.0 {
        cam.radius -= scroll.delta.y as f64 * cam.zoom_speed;
        cam.radius = cam.radius.clamp(cam.min_radius, cam.max_radius);
        cam.is_moving = true;
    }

    if let Some(gamepad) = active_gamepad(&gamepads) {
        let left_stick = stick(gamepad.left_stick());
        if left_stick != Vec2::ZERO {
            let dt = time.delta_secs_f64();
            cam.azimuth += left_stick.x as f64 * GAMEPAD_ORBIT_SPEED * dt;
            cam.elevation -= left_stick.y as f64 * GAMEPAD_ORBIT_SPEED * dt;
            cam.elevation = cam.elevation.clamp(0.01, PI - 0.01);
            cam.is_moving = true;
        }

        let zoom_input = axis(gamepad.get(GamepadButton::RightTrigger2).unwrap_or(0.0))
            - axis(gamepad.get(GamepadButton::LeftTrigger2).unwrap_or(0.0));
        if zoom_input != 0.0 {
            cam.radius -= zoom_input as f64
                * cam.zoom_speed
                * GAMEPAD_ZOOM_SPEED_MULTIPLIER
                * time.delta_secs_f64();
            cam.radius = cam.radius.clamp(cam.min_radius, cam.max_radius);
            cam.is_moving = true;
        }
    }

    if keys.just_pressed(KeyCode::KeyP) {
        cam.polarization_view = (cam.polarization_view + 1) % POLARIZATION_VIEWS.len() as u32;
        cam.is_moving = true;
    }
    if keys.just_pressed(KeyCode::BracketLeft) {
        cam.fov_degrees = (cam.fov_degrees - 5.0).clamp(10.0, 170.0);
        cam.is_moving = true;
    }
    if keys.just_pressed(KeyCode::BracketRight) {
        cam.fov_degrees = (cam.fov_degrees + 5.0).clamp(10.0, 170.0);
        cam.is_moving = true;
    }
}

pub(crate) const ITER_PRESETS: &[u32] = &[8_000, 10_000, 12_000, 14_000, 16_000, 18_000];

/// Press , / . to step the geodesic iteration cap down / up through presets.
fn cycle_max_iter(keys: Res<ButtonInput<KeyCode>>, mut cam: ResMut<OrbitalCamera>) {
    let idx = ITER_PRESETS
        .iter()
        .position(|&x| x == cam.max_iter)
        .unwrap_or(ITER_PRESETS.len() - 1);

    let new_idx = if keys.just_pressed(KeyCode::Comma) {
        idx.saturating_sub(1)
    } else if keys.just_pressed(KeyCode::Period) {
        (idx + 1).min(ITER_PRESETS.len() - 1)
    } else {
        return;
    };

    if new_idx != idx {
        cam.max_iter = ITER_PRESETS[new_idx];
        cam.is_moving = true;
        info!("Max iterations: {}", cam.max_iter);
    }
}

/// Press H to toggle the GPU iteration-count heatmap. Resets TAA history.
fn toggle_heatmap(
    keys: Res<ButtonInput<KeyCode>>,
    gamepads: Query<&Gamepad>,
    mut cam: ResMut<OrbitalCamera>,
) {
    let gamepad_pressed_y =
        active_gamepad(&gamepads).is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::North));
    if keys.just_pressed(KeyCode::KeyH) || gamepad_pressed_y {
        cam.debug_heatmap = !cam.debug_heatmap;
        cam.is_moving = true;
        info!("Heatmap: {}", if cam.debug_heatmap { "ON" } else { "OFF" });
    }
}

fn sync_camera_transform(
    cam: Res<OrbitalCamera>,
    mut query: Query<&mut Transform, With<PerspectiveCamera>>,
) {
    let Ok(mut transform) = query.single_mut() else {
        return;
    };
    *transform = Transform::from_translation(cam.position()).looking_at(Vec3::ZERO, Vec3::Y);
}

#[cfg(test)]
mod tests {
    use super::*;
    use bevy::time::TimeUpdateStrategy;
    use proptest::prelude::*;
    use rstest::rstest;
    use std::time::Duration;

    fn at_elevation(elevation: f64) -> OrbitalCamera {
        OrbitalCamera {
            elevation,
            ..OrbitalCamera::default()
        }
    }

    // ── Orbit geometry ───────────────────────────────────────────────────────

    /// Height as a fraction of the orbit radius at the poles and equator.
    #[rstest]
    #[case::north_pole(0.01, 0.99..=1.0)]
    // f64 cos(π/2) ≈ 6.1e-17; after the f32 cast still negligible.
    #[case::equator(PI * 0.5, -1e-5..=1e-5)]
    #[case::south_pole(PI - 0.01, -1.0..=-0.99)]
    fn elevation_sets_the_height(
        #[case] elevation: f64,
        #[case] expected: std::ops::RangeInclusive<f32>,
    ) {
        let cam = at_elevation(elevation);
        let y = cam.position().y / cam.radius as f32;
        assert!(expected.contains(&y), "y/r = {y}");
    }

    #[rstest]
    #[case(10.0, 5.0_f32.to_radians().tan())]
    #[case(60.0, 30.0_f32.to_radians().tan())]
    #[case(90.0, 1.0)]
    #[case(170.0, 85.0_f32.to_radians().tan())]
    fn tan_half_fov_matches_the_field_of_view(#[case] fov_degrees: f64, #[case] expected: f32) {
        let cam = OrbitalCamera {
            fov_degrees,
            ..OrbitalCamera::default()
        };
        assert!((cam.tan_half_fov() - expected).abs() < 1e-5 * expected);
    }

    proptest! {
        #[test]
        fn position_radius_preserved(
            radius    in 1.6_f64..=160.0_f64,
            azimuth   in -100.0_f64..=100.0_f64,
            elevation in 0.01_f64..=(PI - 0.01),
        ) {
            let cam = OrbitalCamera { radius, azimuth, elevation, ..OrbitalCamera::default() };
            // Compare in f64: cast the f32 position length back up for comparison.
            let rel_err = (cam.position().length() as f64 - radius).abs() / radius;
            prop_assert!(rel_err < 1e-4,
                "position length {} ≠ radius {radius}", cam.position().length());
        }

        #[test]
        fn position_clamps_elevation_short_of_the_poles(beyond in 0.0_f64..10.0) {
            prop_assert_eq!(at_elevation(PI + beyond).position(), at_elevation(PI - 0.01).position());
            prop_assert_eq!(at_elevation(-beyond).position(), at_elevation(0.01).position());
        }

        // Stay 0.1 rad from the poles to avoid the right() singularity where
        // forward ∥ Y and the cross product collapses.
        #[test]
        fn frame_orthonormal_and_facing_the_hole(
            radius    in 1.6_f64..=160.0_f64,
            azimuth   in -100.0_f64..=100.0_f64,
            elevation in 0.1_f64..=(PI - 0.1),
        ) {
            let cam = OrbitalCamera { radius, azimuth, elevation, ..OrbitalCamera::default() };
            let f = cam.forward();
            let r = cam.right();
            let u = cam.up();
            prop_assert!((f.length() - 1.0).abs() < 1e-4, "forward not unit: {}", f.length());
            prop_assert!((r.length() - 1.0).abs() < 1e-4, "right not unit: {}", r.length());
            prop_assert!((u.length() - 1.0).abs() < 1e-4, "up not unit: {}", u.length());
            prop_assert!(f.dot(r).abs() < 1e-3, "forward·right = {}", f.dot(r));
            prop_assert!(f.dot(u).abs() < 1e-3, "forward·up = {}", f.dot(u));
            prop_assert!(r.dot(u).abs() < 1e-3, "right·up = {}", r.dot(u));
            prop_assert!(f.dot(-cam.position().normalize()) > 0.999, "forward misses the origin");
        }

        #[test]
        fn tan_half_fov_always_positive(fov in 10.0_f64..=170.0_f64) {
            let cam = OrbitalCamera { fov_degrees: fov, ..OrbitalCamera::default() };
            prop_assert!(cam.tan_half_fov() > 0.0,
                "tan_half_fov non-positive at {fov}°: {}", cam.tan_half_fov());
        }
    }

    // ── Input systems ────────────────────────────────────────────────────────

    fn input_app() -> App {
        let mut app = App::new();
        app.add_plugins(MinimalPlugins)
            .init_resource::<ButtonInput<KeyCode>>()
            .init_resource::<ButtonInput<MouseButton>>()
            .init_resource::<AccumulatedMouseMotion>()
            .init_resource::<AccumulatedMouseScroll>()
            // The real plugin, so the tests also cover its system ordering.
            .add_plugins(OrbitalCameraPlugin);
        app
    }

    fn app_with(edit: impl FnOnce(&mut OrbitalCamera)) -> App {
        let mut app = input_app();
        edit(&mut app.world_mut().resource_mut::<OrbitalCamera>());
        app
    }

    fn press(app: &mut App, key: KeyCode) -> &OrbitalCamera {
        app.world_mut()
            .resource_mut::<ButtonInput<KeyCode>>()
            .press(key);
        app.update();
        app.world_mut()
            .resource_mut::<ButtonInput<KeyCode>>()
            .reset_all();
        app.world().resource::<OrbitalCamera>()
    }

    fn scroll(app: &mut App, dy: f32) -> &OrbitalCamera {
        app.world_mut()
            .resource_mut::<AccumulatedMouseScroll>()
            .delta = Vec2::new(0.0, dy);
        app.update();
        app.world().resource::<OrbitalCamera>()
    }

    #[rstest]
    #[case::down(10_000, KeyCode::Comma, 8_000)]
    #[case::stops_at_bottom(8_000, KeyCode::Comma, 8_000)]
    #[case::up(10_000, KeyCode::Period, 12_000)]
    #[case::stops_at_top(18_000, KeyCode::Period, 18_000)]
    #[case::off_preset_counts_as_top(12_345, KeyCode::Comma, 16_000)]
    #[case::unbound_key(10_000, KeyCode::KeyK, 10_000)]
    fn iteration_keys_step_through_presets(
        #[case] start: u32,
        #[case] key: KeyCode,
        #[case] expected: u32,
    ) {
        let mut app = app_with(|cam| cam.max_iter = start);
        let cam = press(&mut app, key);
        assert_eq!(cam.max_iter, expected);
        assert_eq!(cam.is_moving, start != expected);
    }

    #[rstest]
    #[case::narrower(60.0, KeyCode::BracketLeft, 55.0)]
    #[case::wider(60.0, KeyCode::BracketRight, 65.0)]
    #[case::clamps_wide(168.0, KeyCode::BracketRight, 170.0)]
    #[case::clamps_narrow(12.0, KeyCode::BracketLeft, 10.0)]
    fn fov_keys_step_by_five_degrees_and_clamp(
        #[case] start: f64,
        #[case] key: KeyCode,
        #[case] expected: f64,
    ) {
        let mut app = app_with(|cam| cam.fov_degrees = start);
        let cam = press(&mut app, key);
        assert_eq!(cam.fov_degrees, expected);
        assert!(cam.is_moving);
    }

    #[rstest]
    #[case::zoom_in(3.0, 36.0)]
    #[case::zoom_out(-2.0, 56.0)]
    #[case::clamps_near(100.0, 1.6)]
    #[case::clamps_far(-100.0, 160.0)]
    fn scroll_zooms_within_radius_limits(#[case] dy: f32, #[case] expected: f64) {
        let mut app = input_app();
        let cam = scroll(&mut app, dy);
        assert_eq!((cam.radius, cam.is_moving), (expected, true));
    }

    #[test]
    fn idle_frame_is_not_moving() {
        let mut app = input_app();
        app.world_mut().resource_mut::<OrbitalCamera>().is_moving = true;
        // Mouse motion without a held button does nothing either.
        app.world_mut()
            .resource_mut::<AccumulatedMouseMotion>()
            .delta = Vec2::new(10.0, 4.0);
        let cam = scroll(&mut app, 0.0);
        assert!(!cam.is_moving && !cam.dragging);
        assert_eq!(cam.azimuth, OrbitalCamera::default().azimuth);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn iteration_keys_walk_the_preset_list(ups in prop::collection::vec(any::<bool>(), 0..12)) {
            let mut app = input_app();
            let mut idx = 1; // the default 10 000 cap
            for up in ups {
                let key = if up { KeyCode::Period } else { KeyCode::Comma };
                idx = if up { (idx + 1).min(ITER_PRESETS.len() - 1) } else { idx.saturating_sub(1) };
                prop_assert_eq!(press(&mut app, key).max_iter, ITER_PRESETS[idx]);
            }
        }

        #[test]
        fn polarization_key_cycles_through_every_view(start in 0..6_u32, presses in 0..20_u32) {
            let mut app = app_with(|cam| cam.polarization_view = start);
            for _ in 0..presses {
                press(&mut app, KeyCode::KeyP);
            }
            prop_assert_eq!(
                app.world().resource::<OrbitalCamera>().polarization_view,
                (start + presses) % POLARIZATION_VIEWS.len() as u32
            );
        }

        #[test]
        fn scrolling_never_leaves_the_radius_limits(deltas in prop::collection::vec(-50.0_f32..50.0, 1..10)) {
            let mut app = input_app();
            for dy in deltas {
                let cam = scroll(&mut app, dy);
                prop_assert!((cam.min_radius..=cam.max_radius).contains(&cam.radius), "{}", cam.radius);
            }
        }

        #[test]
        fn dragging_orbits_by_mouse_delta_and_clamps_elevation(dx in -1e4_f32..1e4, dy in -1e4_f32..1e4) {
            let mut app = input_app();
            app.world_mut().resource_mut::<ButtonInput<MouseButton>>().press(MouseButton::Left);
            app.world_mut().resource_mut::<AccumulatedMouseMotion>().delta = Vec2::new(dx, dy);
            app.update();
            let start = OrbitalCamera::default();
            let cam = app.world().resource::<OrbitalCamera>();
            prop_assert!(cam.dragging);
            prop_assert_eq!(cam.is_moving, dx != 0.0 || dy != 0.0);
            prop_assert!((cam.azimuth - (start.azimuth + dx as f64 * start.orbit_speed)).abs() < 1e-9);
            let elevation = (start.elevation - dy as f64 * start.orbit_speed).clamp(0.01, PI - 0.01);
            prop_assert!((cam.elevation - elevation).abs() < 1e-9);
        }
    }

    #[test]
    fn gamepad_sticks_orbit_and_triggers_zoom() {
        let mut app = input_app();
        app.insert_resource(TimeUpdateStrategy::ManualDuration(Duration::ZERO));
        app.update();
        app.insert_resource(TimeUpdateStrategy::ManualDuration(Duration::from_millis(
            100,
        )));
        let mut gamepad = Gamepad::default();
        gamepad.analog_mut().set(GamepadAxis::LeftStickX, 0.5);
        gamepad.analog_mut().set(GamepadAxis::LeftStickY, -0.25);
        gamepad.analog_mut().set(GamepadButton::RightTrigger2, 0.75);
        gamepad.analog_mut().set(GamepadButton::LeftTrigger2, 0.25);
        let pad = app.world_mut().spawn(gamepad).id();
        app.update();

        let start = OrbitalCamera::default();
        let cam = app.world().resource::<OrbitalCamera>();
        let dt = 0.1;
        assert!((cam.azimuth - (start.azimuth + 0.5 * GAMEPAD_ORBIT_SPEED * dt)).abs() < 1e-6);
        assert!((cam.elevation - (start.elevation + 0.25 * GAMEPAD_ORBIT_SPEED * dt)).abs() < 1e-6);
        let zoom = 0.5 * start.zoom_speed * GAMEPAD_ZOOM_SPEED_MULTIPLIER * dt;
        assert!((cam.radius - (start.radius - zoom)).abs() < 1e-6);
        assert!(cam.is_moving);

        // Input inside the deadzone leaves the camera alone.
        let mut idle = Gamepad::default();
        idle.analog_mut().set(GamepadAxis::LeftStickX, 0.1);
        idle.analog_mut().set(GamepadButton::LeftTrigger2, 0.1);
        app.world_mut().entity_mut(pad).insert(idle);
        let before = app.world().resource::<OrbitalCamera>().radius;
        app.update();
        let cam = app.world().resource::<OrbitalCamera>();
        assert_eq!(cam.radius, before);
        assert!(!cam.is_moving);

        // Extreme stick input clamps elevation like mouse dragging does.
        let mut extreme = Gamepad::default();
        extreme.analog_mut().set(GamepadAxis::LeftStickY, -1.0);
        app.world_mut().entity_mut(pad).insert(extreme);
        app.world_mut().resource_mut::<OrbitalCamera>().elevation = PI - 0.02;
        app.update();
        assert_eq!(app.world().resource::<OrbitalCamera>().elevation, PI - 0.01);
    }

    #[rstest]
    #[case::turns_on(false)]
    #[case::turns_off(true)]
    fn heatmap_key_toggles(#[case] start: bool) {
        let mut app = App::new();
        app.init_resource::<ButtonInput<KeyCode>>()
            .insert_resource(OrbitalCamera {
                debug_heatmap: start,
                ..default()
            })
            .add_systems(Update, toggle_heatmap);
        let cam = press(&mut app, KeyCode::KeyH);
        assert_eq!(cam.debug_heatmap, !start);
        assert!(cam.is_moving);
    }

    #[test]
    fn grid_camera_follows_the_orbit_and_looks_at_the_hole() {
        let mut app = App::new();
        app.init_resource::<OrbitalCamera>()
            .add_systems(Update, sync_camera_transform);
        let entity = app
            .world_mut()
            .spawn((Transform::default(), PerspectiveCamera))
            .id();
        app.update();
        let cam = app.world().resource::<OrbitalCamera>();
        let transform = app.world().get::<Transform>(entity).unwrap();
        assert_eq!(transform.translation, cam.position());
        assert!(transform.forward().dot(cam.forward()) > 0.9999);
    }
}
