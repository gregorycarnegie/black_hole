use bevy::{
    diagnostic::{DiagnosticsStore, FrameTimeDiagnosticsPlugin},
    prelude::*,
};

mod bridge;
mod camera;
mod compute;
mod controller;
mod grid;
mod simulation;
mod swarm;
mod ui;

fn main() {
    let profiling = std::env::args_os().any(|arg| arg == "--profile-renderer");
    // Turns off guarded single-Kerr early capture, which is on by default.
    let full_trace = std::env::args_os().any(|arg| arg == "--full-trace");
    // Capped steps far from the hole, kept for one release after far-field steps became
    // the default (checklist P1.8).
    let no_far_field = std::env::args_os().any(|arg| arg == "--no-far-field");
    // The step-doubling RK4 controller, kept for one release after Dormand–Prince became the default.
    let rk4 = std::env::args_os().any(|arg| arg == "--rk4-controller");
    // One midpoint transfer cell per geodesic step, kept for one release after decoupled
    // transfer became the default (checklist P1.9).
    let coupled_transfer = std::env::args_os().any(|arg| arg == "--coupled-transfer");
    // Numerical steps outside the disk's enclosing sphere, kept for one release after
    // analytic vacuum legs became the default (checklist P1.8).
    let no_analytic_legs = std::env::args_os().any(|arg| arg == "--no-analytic-legs");
    // Analytic legs inside that sphere too, up to the band around a thin disk: fewer
    // steps but no faster on the tested GPU (checklist P1.8).
    let band_legs = std::env::args_os().any(|arg| arg == "--band-legs");
    let mut window = Window {
        title: "Black Hole".into(),
        resolution: (800u32, 600u32).into(),
        ..default()
    };
    if profiling {
        window.present_mode = bevy::window::PresentMode::AutoNoVsync;
        window.resolution = window.resolution.with_scale_factor_override(1.0);
        window.resizable = false;
    }
    let mut app = App::new();
    app.add_plugins(DefaultPlugins.set(WindowPlugin {
        primary_window: Some(window),
        ..default()
    }))
    .add_plugins(FrameTimeDiagnosticsPlugin::default())
    .add_plugins(camera::OrbitalCameraPlugin)
    .add_plugins(simulation::SimulationPlugin)
    .add_plugins(swarm::SwarmPlugin)
    .add_plugins(bridge::BridgePlugin)
    .add_plugins(grid::GridPlugin)
    .add_plugins(compute::GeodesicComputePlugin)
    .add_plugins(ui::UiPlugin)
    .add_systems(Startup, setup_fps_ui)
    .add_systems(Update, update_fps_text);
    if profiling {
        compute::profile::install(&mut app);
    }
    if full_trace || no_far_field || rk4 || coupled_transfer || no_analytic_legs || band_legs {
        compute::enable_ray_experiments(
            &mut app,
            full_trace,
            no_far_field,
            rk4,
            coupled_transfer,
            no_analytic_legs,
            band_legs,
        );
    }
    app.run();
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
            font_size: FontSize::Px(14.0),
            ..default()
        },
        TextColor(Color::WHITE),
        FpsText,
    ));
}

fn update_fps_text(diagnostics: Res<DiagnosticsStore>, mut query: Query<&mut Text, With<FpsText>>) {
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
