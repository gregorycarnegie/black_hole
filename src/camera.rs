use bevy::{
    input::mouse::{AccumulatedMouseMotion, AccumulatedMouseScroll},
    prelude::*,
};
use std::f32::consts::PI;

pub struct OrbitalCameraPlugin;

impl Plugin for OrbitalCameraPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<OrbitalCamera>()
            .add_systems(Startup, setup_cameras)
            .add_systems(Update, update_orbital_camera)
            .add_systems(Update, sync_camera_transform.after(update_orbital_camera));
    }
}

/// Tracks the logical orbital camera state. Updated from mouse/keyboard input
/// each frame, then synced to the actual Bevy Camera3d transform.
#[derive(Resource)]
pub struct OrbitalCamera {
    pub radius: f32,
    pub azimuth: f32,
    pub elevation: f32,
    pub min_radius: f32,
    pub max_radius: f32,
    pub orbit_speed: f32,
    pub zoom_speed: f32,
    pub dragging: bool,
    pub is_moving: bool,
}

impl Default for OrbitalCamera {
    fn default() -> Self {
        Self {
            radius: 6.34194e10,
            azimuth: 0.0,
            elevation: PI / 2.0,
            min_radius: 1e10,
            max_radius: 1e12,
            orbit_speed: 0.005,
            zoom_speed: 25e9,
            dragging: false,
            is_moving: false,
        }
    }
}

impl OrbitalCamera {
    pub fn position(&self) -> Vec3 {
        let elev = self.elevation.clamp(0.01, PI - 0.01);
        Vec3::new(
            self.radius * elev.sin() * self.azimuth.cos(),
            self.radius * elev.cos(),
            self.radius * elev.sin() * self.azimuth.sin(),
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
        (60.0_f32.to_radians() * 0.5).tan()
    }

    pub fn aspect(&self) -> f32 {
        800.0 / 600.0
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
    commands.spawn((Camera2d, Camera { order: 0, ..default() }, BackgroundCamera));

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
) {
    cam.dragging = mouse_button.pressed(MouseButton::Left);
    cam.is_moving = false;

    if cam.dragging && mouse_motion.delta != Vec2::ZERO {
        cam.azimuth += mouse_motion.delta.x * cam.orbit_speed;
        cam.elevation -= mouse_motion.delta.y * cam.orbit_speed;
        cam.elevation = cam.elevation.clamp(0.01, PI - 0.01);
        cam.is_moving = true;
    }

    if scroll.delta.y != 0.0 {
        cam.radius -= scroll.delta.y * cam.zoom_speed;
        cam.radius = cam.radius.clamp(cam.min_radius, cam.max_radius);
        cam.is_moving = true;
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
