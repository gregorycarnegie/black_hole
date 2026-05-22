use bevy::prelude::*;

use crate::{camera::OrbitalCamera, simulation::{C, G_CONST, SimObjects}};

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

fn toggle_grid(keys: Res<ButtonInput<KeyCode>>, mut visible: ResMut<GridVisible>) {
    if keys.just_pressed(KeyCode::KeyF) {
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
    if radius < 1.5e11 {
        (25, 1.0e10) // 626 verts, 1250 segments
    } else if radius < 5.0e11 {
        (13, 2.0e10) // 196 verts,  338 segments
    } else {
        (9,  4.0e10) //  100 verts,  162 segments
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
                    let r_s = (2.0 * G_CONST * obj.mass as f64 / (C * C)) as f32;
                    let dx = world_x - obj.position.x;
                    let dz = world_z - obj.position.z;
                    let dist = (dx * dx + dz * dz).sqrt();
                    y += 2.0 * (r_s * (dist - r_s).max(0.0)).sqrt() - 3e10;
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
