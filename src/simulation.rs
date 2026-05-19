use bevy::prelude::*;

pub const C: f64 = 299_792_458.0;
pub const G_CONST: f64 = 6.6743e-11;
pub const SAGA_MASS: f64 = 8.54e36;
// Schwarzschild radius of Sag A* in meters
pub const _SAGA_RS: f32 = 1.269e10;

pub struct SimulationPlugin;

impl Plugin for SimulationPlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<SimObjects>()
            .init_resource::<GravityEnabled>()
            .add_systems(Update, (toggle_gravity, gravity_system).chain());
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
        let sag_rs = (2.0 * G_CONST * SAGA_MASS / (C * C)) as f32;
        Self(vec![
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
            // Black hole at origin (last so objects loop skips it for gravity source)
            SimObject {
                position: Vec3::ZERO,
                radius: sag_rs,
                color: Vec4::new(0., 0., 0., 1.),
                mass: SAGA_MASS as f32,
                velocity: Vec3::ZERO,
            },
        ])
    }
}

#[derive(Resource, Default)]
pub struct GravityEnabled(pub bool);

fn toggle_gravity(keys: Res<ButtonInput<KeyCode>>, mut gravity: ResMut<GravityEnabled>) {
    if keys.just_pressed(KeyCode::KeyG) {
        gravity.0 = !gravity.0;
        info!("Gravity: {}", if gravity.0 { "ON" } else { "OFF" });
    }
}

fn gravity_system(mut objects: ResMut<SimObjects>, gravity: Res<GravityEnabled>) {
    if !gravity.0 {
        return;
    }

    let n = objects.0.len();
    let mut accelerations = vec![Vec3::ZERO; n];

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let diff = objects.0[j].position - objects.0[i].position;
            let dist = diff.length();
            if dist > 0.0 {
                let force = (G_CONST as f32 * objects.0[i].mass * objects.0[j].mass) / (dist * dist);
                let acc = force / objects.0[i].mass;
                accelerations[i] += diff.normalize() * acc;
            }
        }
    }

    for (i, obj) in objects.0.iter_mut().enumerate() {
        obj.velocity += accelerations[i];
        obj.position += obj.velocity;
    }
}
