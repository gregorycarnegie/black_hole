use bevy::{
    input::mouse::{AccumulatedMouseMotion, AccumulatedMouseScroll},
    prelude::*,
};
use std::f64::consts::PI;

pub struct OrbitalCameraPlugin;

impl Plugin for OrbitalCameraPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<OrbitalCamera>()
            .add_systems(Startup, setup_cameras)
            .add_systems(
                Update,
                (update_orbital_camera, toggle_heatmap, cycle_max_iter),
            )
            .add_systems(Update, sync_camera_transform.after(update_orbital_camera));
    }
}

/// Tracks the logical orbital camera state. Updated from mouse/keyboard input
/// each frame, then synced to the actual Bevy Camera3d transform.
///
/// Orbital parameters (`radius`, `azimuth`, `elevation`) are stored as `f64`
/// so that accumulated mouse/scroll input doesn't lose precision when the
/// camera is very close to the event horizon (~1e10 m). The GPU uniform is
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
}

impl Default for OrbitalCamera {
    fn default() -> Self {
        Self {
            radius: 3.0e11,
            azimuth: 0.0,
            elevation: PI / 2.0 - 0.35,
            min_radius: 1e10,
            max_radius: 1e12,
            orbit_speed: 0.005,
            zoom_speed: 25e9,
            fov_degrees: 60.0,
            dragging: false,
            is_moving: false,
            debug_heatmap: false,
            max_iter: 10_000,
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

    if keys.just_pressed(KeyCode::BracketLeft) {
        cam.fov_degrees = (cam.fov_degrees - 5.0).clamp(10.0, 170.0);
        cam.is_moving = true;
    }
    if keys.just_pressed(KeyCode::BracketRight) {
        cam.fov_degrees = (cam.fov_degrees + 5.0).clamp(10.0, 170.0);
        cam.is_moving = true;
    }
}

const ITER_PRESETS: &[u32] = &[8_000, 10_000, 12_000, 14_000, 16_000, 18_000];

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
fn toggle_heatmap(keys: Res<ButtonInput<KeyCode>>, mut cam: ResMut<OrbitalCamera>) {
    if keys.just_pressed(KeyCode::KeyH) {
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
    use proptest::prelude::*;

    // ── Unit tests ───────────────────────────────────────────────────────────

    #[test]
    fn position_length_equals_radius() {
        let cam = OrbitalCamera::default();
        let pos = cam.position();
        let rel_err = (pos.length() as f64 - cam.radius).abs() / cam.radius;
        assert!(
            rel_err < 1e-5,
            "position length {} ≠ radius {}",
            pos.length(),
            cam.radius
        );
    }

    #[test]
    fn frame_is_orthonormal_at_default() {
        let cam = OrbitalCamera::default();
        let f = cam.forward();
        let r = cam.right();
        let u = cam.up();
        assert!(
            (f.length() - 1.0).abs() < 1e-5,
            "forward not unit: {}",
            f.length()
        );
        assert!(
            (r.length() - 1.0).abs() < 1e-5,
            "right not unit: {}",
            r.length()
        );
        assert!(
            (u.length() - 1.0).abs() < 1e-5,
            "up not unit: {}",
            u.length()
        );
        assert!(f.dot(r).abs() < 1e-5, "forward·right = {}", f.dot(r));
        assert!(f.dot(u).abs() < 1e-5, "forward·up = {}", f.dot(u));
        assert!(r.dot(u).abs() < 1e-5, "right·up = {}", r.dot(u));
    }

    #[test]
    fn forward_points_toward_origin() {
        let cam = OrbitalCamera::default();
        let pos = cam.position();
        let dot = cam.forward().dot((-pos).normalize());
        assert!(
            dot > 0.999,
            "forward should point toward origin, got dot={dot}"
        );
    }

    #[test]
    fn tan_half_fov_positive_for_valid_range() {
        for &deg in &[10.0_f64, 30.0, 60.0, 90.0, 120.0, 170.0] {
            let cam = OrbitalCamera {
                fov_degrees: deg,
                ..OrbitalCamera::default()
            };
            assert!(
                cam.tan_half_fov() > 0.0,
                "tan_half_fov non-positive at {deg}°"
            );
        }
    }

    #[test]
    fn north_pole_has_positive_y() {
        let cam = OrbitalCamera {
            elevation: 0.01,
            ..OrbitalCamera::default()
        };
        assert!(cam.position().y > 0.0, "north pole should have positive y");
    }

    #[test]
    fn south_pole_has_negative_y() {
        let cam = OrbitalCamera {
            elevation: PI - 0.01,
            ..OrbitalCamera::default()
        };
        assert!(cam.position().y < 0.0, "south pole should have negative y");
    }

    #[test]
    fn equator_has_near_zero_y() {
        let cam = OrbitalCamera {
            elevation: PI * 0.5,
            ..OrbitalCamera::default()
        };
        // f64 cos(π/2) ≈ 6.1e-17; after f32 cast still negligible relative to radius.
        let rel_err = cam.position().y.abs() as f64 / cam.radius;
        assert!(rel_err < 1e-5, "equator y not near zero: rel_err={rel_err}");
    }

    // ── Proptest ─────────────────────────────────────────────────────────────

    proptest! {
        #[test]
        fn position_radius_preserved(
            radius    in 1e10_f64..=1e12_f64,
            azimuth   in -100.0_f64..=100.0_f64,
            elevation in 0.01_f64..=(PI - 0.01),
        ) {
            let cam = OrbitalCamera { radius, azimuth, elevation, ..OrbitalCamera::default() };
            // Compare in f64: cast the f32 position length back up for comparison.
            let rel_err = (cam.position().length() as f64 - radius).abs() / radius;
            prop_assert!(rel_err < 1e-4,
                "position length {} ≠ radius {radius}", cam.position().length());
        }

        // Stay 0.1 rad from the poles to avoid the right() singularity where
        // forward ∥ Y and the cross product collapses.
        #[test]
        fn frame_orthonormal_across_orientations(
            radius    in 1e10_f64..=1e12_f64,
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
        }

        #[test]
        fn tan_half_fov_always_positive(fov in 10.0_f64..=170.0_f64) {
            let cam = OrbitalCamera { fov_degrees: fov, ..OrbitalCamera::default() };
            prop_assert!(cam.tan_half_fov() > 0.0,
                "tan_half_fov non-positive at {fov}°: {}", cam.tan_half_fov());
        }
    }
}
