use bevy::prelude::*;

mod camera;
mod compute;
mod grid;
mod simulation;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Black Hole".into(),
                resolution: (800u32, 600u32).into(),
                ..default()
            }),
            ..default()
        }))
        .add_plugins(camera::OrbitalCameraPlugin)
        .add_plugins(simulation::SimulationPlugin)
        .add_plugins(grid::GridPlugin)
        .add_plugins(compute::GeodesicComputePlugin)
        .run();
}
