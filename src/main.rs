use bevy::{
    diagnostic::{DiagnosticsStore, FrameTimeDiagnosticsPlugin},
    prelude::*,
};

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
        .add_plugins(FrameTimeDiagnosticsPlugin::default())
        .add_plugins(camera::OrbitalCameraPlugin)
        .add_plugins(simulation::SimulationPlugin)
        .add_plugins(grid::GridPlugin)
        .add_plugins(compute::GeodesicComputePlugin)
        .add_systems(Startup, setup_fps_ui)
        .add_systems(Update, update_fps_text)
        .run();
}

/// Marker for the on-screen FPS counter.
#[derive(Component)]
struct FpsText;

fn setup_fps_ui(mut commands: Commands) {
    commands.spawn((
        Node {
            position_type: PositionType::Absolute,
            top: Val::Px(8.0),
            left: Val::Px(8.0),
            ..default()
        },
        Text::new("FPS: --"),
        TextFont {
            font_size: 14.0,
            ..default()
        },
        TextColor(Color::WHITE),
        FpsText,
    ));
}

fn update_fps_text(
    diagnostics: Res<DiagnosticsStore>,
    mut query: Query<&mut Text, With<FpsText>>,
) {
    let Ok(mut text) = query.single_mut() else {
        return;
    };
    if let Some(fps) = diagnostics
        .get(&FrameTimeDiagnosticsPlugin::FPS)
        .and_then(|d| d.smoothed())
    {
        **text = format!("FPS: {fps:.0}");
    }
}
