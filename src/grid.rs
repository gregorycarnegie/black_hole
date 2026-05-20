use bevy::prelude::*;

use crate::simulation::{G_CONST, SimObjects};

pub struct GridPlugin;

impl Plugin for GridPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<GridCache>()
            .add_systems(Update, draw_spacetime_grid);
    }
}

#[derive(Resource, Default)]
struct GridCache {
    verts: Vec<Vec3>,
}

/// Draws a 25×25 wireframe grid deformed by the Schwarzschild metric of each
/// object. Vertices are cached and only recomputed when object positions change.
fn draw_spacetime_grid(
    mut gizmos: Gizmos,
    objects: Res<SimObjects>,
    mut cache: ResMut<GridCache>,
) {
    const GRID_SIZE: i32 = 25;
    const SPACING: f32 = 1e10;
    const C: f64 = 299_792_458.0;

    let count = (GRID_SIZE + 1) as usize;

    if objects.is_changed() || cache.verts.is_empty() {
        cache.verts.resize(count * count, Vec3::ZERO);

        for zi in 0..=GRID_SIZE {
            for xi in 0..=GRID_SIZE {
                let world_x = (xi - GRID_SIZE / 2) as f32 * SPACING;
                let world_z = (zi - GRID_SIZE / 2) as f32 * SPACING;
                let mut y = 0.0_f32;

                for obj in &objects.0 {
                    let r_s = (2.0 * G_CONST * obj.mass as f64 / (C * C)) as f32;
                    let dx = world_x - obj.position.x;
                    let dz = world_z - obj.position.z;
                    let dist = (dx * dx + dz * dz).sqrt();

                    y += 2.0 * (r_s * (dist - r_s).max(0.0)).sqrt() - 3e10;
                }

                cache.verts[zi as usize * count + xi as usize] =
                    Vec3::new(world_x, y, world_z);
            }
        }
    }

    let color = Color::srgba(0.3, 0.6, 1.0, 0.4);

    // Horizontal lines (along X for each Z row)
    for zi in 0..=GRID_SIZE {
        for xi in 0..GRID_SIZE {
            let a = cache.verts[zi as usize * count + xi as usize];
            let b = cache.verts[zi as usize * count + xi as usize + 1];
            gizmos.line(a, b, color);
        }
    }

    // Vertical lines (along Z for each X column)
    for zi in 0..GRID_SIZE {
        for xi in 0..=GRID_SIZE {
            let a = cache.verts[zi as usize * count + xi as usize];
            let b = cache.verts[(zi as usize + 1) * count + xi as usize];
            gizmos.line(a, b, color);
        }
    }
}
