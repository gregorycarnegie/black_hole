use bevy::prelude::*;

use crate::{camera::OrbitalCamera, controller::active_gamepad, simulation::SimObjects};

pub struct GridPlugin;

impl Plugin for GridPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<GridCache>()
            .init_resource::<GridVisible>()
            .add_systems(Update, (toggle_grid, draw_spacetime_grid).chain());
    }
}

/// Press F to show/hide the spacetime grid.
#[derive(Resource)]
pub struct GridVisible(pub bool);

impl Default for GridVisible {
    fn default() -> Self {
        Self(true)
    }
}

fn toggle_grid(
    keys: Res<ButtonInput<KeyCode>>,
    gamepads: Query<&Gamepad>,
    mut visible: ResMut<GridVisible>,
) {
    let gamepad_pressed_x =
        active_gamepad(&gamepads).is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::West));
    if keys.just_pressed(KeyCode::KeyF) || gamepad_pressed_x {
        visible.0 = !visible.0;
        info!("Grid: {}", if visible.0 { "visible" } else { "hidden" });
    }
}

#[derive(Resource, Default)]
struct GridCache {
    verts: Vec<Vec3>,
    /// GRID_SIZE used when verts were last computed. 0 forces initial build.
    grid_size: i32,
}

/// Returns (grid_size, spacing) for the current camera distance.
/// Closer camera → finer grid; farther → coarser grid with wider spacing
/// so the scene fills roughly the same visual area.
fn grid_lod(radius: f64) -> (i32, f32) {
    if radius < 24.0 {
        (25, 1.6) // 626 verts, 1250 segments
    } else if radius < 80.0 {
        (13, 3.2) // 196 verts,  338 segments
    } else {
        (9, 6.4) //  100 verts,  162 segments
    }
}

/// Draws a wireframe grid deformed by the Schwarzschild metric of each object.
/// Vertices are cached and only recomputed when object positions or LOD change.
fn draw_spacetime_grid(
    mut gizmos: Gizmos,
    objects: Res<SimObjects>,
    cam: Res<OrbitalCamera>,
    mut cache: ResMut<GridCache>,
    visible: Res<GridVisible>,
) {
    if !visible.0 {
        return;
    }

    let (grid_size, spacing) = grid_lod(cam.radius);
    let count = (grid_size + 1) as usize;

    if objects.is_changed() || cache.verts.is_empty() || cache.grid_size != grid_size {
        cache.grid_size = grid_size;
        cache.verts.resize(count * count, Vec3::ZERO);

        for zi in 0..=grid_size {
            for xi in 0..=grid_size {
                let world_x = (xi - grid_size / 2) as f32 * spacing;
                let world_z = (zi - grid_size / 2) as f32 * spacing;
                let mut y = 0.0_f32;

                for obj in &objects.0 {
                    let r_s = 2.0 * obj.mass;
                    let dx = world_x - obj.position.x;
                    let dz = world_z - obj.position.z;
                    let dist = (dx * dx + dz * dz).sqrt();
                    y += 2.0 * (r_s * (dist - r_s).max(0.0)).sqrt() - 4.8;
                }

                cache.verts[zi as usize * count + xi as usize] = Vec3::new(world_x, y, world_z);
            }
        }
    }

    let color = Color::srgba(0.3, 0.6, 1.0, 0.4);

    for zi in 0..=grid_size {
        for xi in 0..grid_size {
            let a = cache.verts[zi as usize * count + xi as usize];
            let b = cache.verts[zi as usize * count + xi as usize + 1];
            gizmos.line(a, b, color);
        }
    }

    for zi in 0..grid_size {
        for xi in 0..=grid_size {
            let a = cache.verts[zi as usize * count + xi as usize];
            let b = cache.verts[(zi as usize + 1) * count + xi as usize];
            gizmos.line(a, b, color);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use rstest::rstest;

    #[rstest]
    #[case(1.6, (25, 1.6))]
    #[case(23.9, (25, 1.6))]
    #[case(24.0, (13, 3.2))]
    #[case(79.9, (13, 3.2))]
    #[case(80.0, (9, 6.4))]
    #[case(160.0, (9, 6.4))]
    fn grid_gets_coarser_as_the_camera_backs_off(
        #[case] radius: f64,
        #[case] expected: (i32, f32),
    ) {
        assert_eq!(grid_lod(radius), expected);
    }

    proptest! {
        /// Coarser levels widen their spacing so the grid covers roughly the same area.
        #[test]
        fn zooming_out_never_refines_or_shrinks_the_grid(near in 1.6_f64..160.0, gap in 0.0_f64..160.0) {
            let (near_size, near_spacing) = grid_lod(near);
            let (far_size, far_spacing) = grid_lod(near + gap);
            prop_assert!(far_size <= near_size);
            prop_assert!(far_spacing >= near_spacing);
            prop_assert!(far_size as f32 * far_spacing >= near_size as f32 * near_spacing * 0.9);
        }
    }

    #[rstest]
    #[case::shows_hidden_grid(false, true)]
    #[case::hides_visible_grid(true, false)]
    fn f_key_toggles_grid_visibility(#[case] visible: bool, #[case] expected: bool) {
        let mut app = App::new();
        app.init_resource::<ButtonInput<KeyCode>>()
            .insert_resource(GridVisible(visible))
            .add_systems(Update, toggle_grid);
        app.world_mut()
            .resource_mut::<ButtonInput<KeyCode>>()
            .press(KeyCode::KeyF);
        app.update();
        assert_eq!(app.world().resource::<GridVisible>().0, expected);
    }
}
