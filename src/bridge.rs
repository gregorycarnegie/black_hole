use bevy::{
    picking::hover::Hovered,
    prelude::*,
    render::extract_resource::{ExtractResource, ExtractResourcePlugin},
    ui::Pressed,
    ui_widgets::Button,
};
use black_hole::einstein_rosen::{MAX_TIME, profile};

use crate::{camera::OrbitalCamera, ui::BlackHoleControls};

pub struct BridgePlugin;

impl Plugin for BridgePlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<BridgeView>()
            .add_plugins(ExtractResourcePlugin::<BridgeView>::default())
            .add_systems(Startup, setup_controls)
            .add_systems(Update, update_controls.in_set(BridgeInput))
            .add_systems(Update, draw_bridge.after(BridgeInput));
    }
}

#[derive(SystemSet, Debug, Clone, PartialEq, Eq, Hash)]
pub struct BridgeInput;

#[derive(Resource, Clone, ExtractResource)]
#[extract_app(bevy::render::RenderApp)]
pub struct BridgeView {
    pub mode: SimulationView,
    time: f64,
    playing: bool,
    saved_camera: Option<[f64; 3]>,
    pub matter_enabled: bool,
    pub matter_time: f64,
    matter_playing: bool,
}

impl Default for BridgeView {
    fn default() -> Self {
        Self {
            mode: SimulationView::default(),
            time: 0.0,
            playing: false,
            saved_camera: None,
            matter_enabled: true,
            matter_time: 0.0,
            matter_playing: true,
        }
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub enum SimulationView {
    #[default]
    BlackHoles,
    Ellis,
    EinsteinRosen,
}

pub fn black_hole_view(view: Option<Res<BridgeView>>) -> bool {
    view.is_none_or(|view| view.mode == SimulationView::BlackHoles)
}

pub fn ray_traced_view(view: Option<Res<BridgeView>>) -> bool {
    view.is_none_or(|view| view.mode != SimulationView::EinsteinRosen)
}

#[derive(Component, Clone, Copy)]
enum BridgeAction {
    Toggle,
    Earlier,
    Later,
    Play,
    Reset,
    ToggleMatter,
}

#[derive(Component)]
struct BridgeStatus;

fn setup_controls(mut commands: Commands) {
    commands
        .spawn((
            Node {
                position_type: PositionType::Absolute,
                left: Val::Px(8.0),
                bottom: Val::Px(8.0),
                max_width: Val::Percent(96.0),
                flex_direction: FlexDirection::Column,
                row_gap: Val::Px(6.0),
                padding: UiRect::all(Val::Px(8.0)),
                ..default()
            },
            BackgroundColor(Color::srgba(0.02, 0.03, 0.05, 0.95)),
        ))
        .with_children(|panel| {
            panel.spawn((
                Text::new(""),
                TextFont {
                    font_size: FontSize::Px(13.0),
                    ..default()
                },
                TextColor(Color::WHITE),
                BridgeStatus,
            ));
            panel
                .spawn(Node {
                    column_gap: Val::Px(6.0),
                    ..default()
                })
                .with_children(|row| {
                    for (label, action) in [
                        ("Switch simulation [W]", BridgeAction::Toggle),
                        ("Earlier [Left]", BridgeAction::Earlier),
                        ("Later [Right]", BridgeAction::Later),
                        ("Play/pause [Space]", BridgeAction::Play),
                        ("Reset [R]", BridgeAction::Reset),
                        ("Matter [D]", BridgeAction::ToggleMatter),
                    ] {
                        row.spawn((
                            Button,
                            Hovered::default(),
                            action,
                            Node {
                                padding: UiRect::all(Val::Px(6.0)),
                                ..default()
                            },
                            BackgroundColor(Color::srgb(0.12, 0.18, 0.26)),
                        ))
                        .with_children(|button| {
                            button.spawn((
                                Text::new(label),
                                TextFont {
                                    font_size: FontSize::Px(12.0),
                                    ..default()
                                },
                                TextColor(Color::WHITE),
                            ));
                        });
                    }
                });
        });
}

fn apply_action(view: &mut BridgeView, cam: &mut OrbitalCamera, action: BridgeAction) {
    match action {
        BridgeAction::Toggle => {
            if view.mode == SimulationView::BlackHoles {
                view.saved_camera = Some([cam.radius, cam.elevation, cam.min_radius]);
            }
            view.mode = match view.mode {
                SimulationView::BlackHoles => SimulationView::Ellis,
                SimulationView::Ellis => SimulationView::EinsteinRosen,
                SimulationView::EinsteinRosen => SimulationView::BlackHoles,
            };
            match view.mode {
                SimulationView::Ellis => {
                    cam.radius = 12.0;
                    cam.min_radius = 0.05;
                }
                SimulationView::EinsteinRosen => {
                    cam.radius = 48.0;
                    cam.elevation = 1.1;
                    cam.min_radius = 6.0;
                }
                SimulationView::BlackHoles => {
                    if let Some([radius, elevation, min_radius]) = view.saved_camera.take() {
                        cam.radius = radius;
                        cam.elevation = elevation;
                        cam.min_radius = min_radius;
                    }
                }
            }
            cam.is_moving = true;
        }
        BridgeAction::Earlier | BridgeAction::Later
            if view.mode == SimulationView::EinsteinRosen =>
        {
            let delta = if matches!(action, BridgeAction::Earlier) {
                -0.05
            } else {
                0.05
            };
            view.time = (view.time + delta).clamp(-MAX_TIME, MAX_TIME);
            view.playing = false;
        }
        BridgeAction::Play if view.mode == SimulationView::EinsteinRosen => {
            if view.time >= MAX_TIME {
                view.time = -MAX_TIME;
            }
            view.playing = !view.playing;
        }
        BridgeAction::Reset if view.mode == SimulationView::EinsteinRosen => {
            view.time = 0.0;
            view.playing = false;
        }
        BridgeAction::ToggleMatter if view.mode == SimulationView::Ellis => {
            view.matter_enabled = !view.matter_enabled;
            cam.is_moving = true;
        }
        BridgeAction::Play if view.mode == SimulationView::Ellis && view.matter_enabled => {
            view.matter_playing = !view.matter_playing;
            cam.is_moving = true;
        }
        BridgeAction::Reset if view.mode == SimulationView::Ellis => {
            view.matter_time = 0.0;
            cam.is_moving = true;
        }
        _ => {}
    }
}

fn update_controls(
    keys: Res<ButtonInput<KeyCode>>,
    time: Res<Time>,
    mut view: ResMut<BridgeView>,
    mut cam: ResMut<OrbitalCamera>,
    buttons: Query<&BridgeAction, (Added<Pressed>, With<Button>)>,
) {
    for (key, action) in [
        (KeyCode::KeyW, BridgeAction::Toggle),
        (KeyCode::ArrowLeft, BridgeAction::Earlier),
        (KeyCode::ArrowRight, BridgeAction::Later),
        (KeyCode::Space, BridgeAction::Play),
        (KeyCode::KeyR, BridgeAction::Reset),
        (KeyCode::KeyD, BridgeAction::ToggleMatter),
    ] {
        if keys.just_pressed(key) {
            apply_action(&mut view, &mut cam, action);
        }
    }
    for action in &buttons {
        apply_action(&mut view, &mut cam, *action);
    }
    if view.mode == SimulationView::EinsteinRosen && view.playing {
        view.time = (view.time + time.delta_secs_f64() * 0.2).min(MAX_TIME);
        if view.time >= MAX_TIME {
            view.playing = false;
        }
    }
    if view.mode == SimulationView::Ellis && view.matter_enabled && view.matter_playing {
        view.matter_time += time.delta_secs_f64();
    }
}

fn draw_bridge(
    view: Res<BridgeView>,
    mut gizmos: Gizmos,
    mut status: Query<&mut Text, With<BridgeStatus>>,
    mut panels: Query<&mut Node, With<BlackHoleControls>>,
    mut buttons: Query<
        (&BridgeAction, &Hovered, &mut Node, &mut BackgroundColor),
        Without<BlackHoleControls>,
    >,
) {
    for mut panel in &mut panels {
        panel.display = if view.mode != SimulationView::BlackHoles {
            Display::None
        } else {
            Display::Flex
        };
    }
    for (action, hovered, mut node, mut color) in &mut buttons {
        let shown = match action {
            BridgeAction::Toggle => true,
            BridgeAction::ToggleMatter => view.mode == SimulationView::Ellis,
            BridgeAction::Play | BridgeAction::Reset => view.mode != SimulationView::BlackHoles,
            BridgeAction::Earlier | BridgeAction::Later => {
                view.mode == SimulationView::EinsteinRosen
            }
        };
        node.display = if shown { Display::Flex } else { Display::None };
        color.0 = if hovered.get() {
            Color::srgb(0.22, 0.32, 0.45)
        } else {
            Color::srgb(0.12, 0.18, 0.26)
        };
    }
    if view.mode != SimulationView::EinsteinRosen {
        for mut text in &mut status {
            **text = if view.mode == SimulationView::Ellis {
                format!(
                    "Ellis wormhole | Dust {} | t={:.1} | pulse center l={:.1}\nPressureless test matter on fixed geometry | B: sky pairs | Drag/scroll: camera",
                    if !view.matter_enabled {
                        "off"
                    } else if view.matter_playing {
                        "playing"
                    } else {
                        "paused"
                    },
                    view.matter_time,
                    8.0 - 0.5 * view.matter_time
                )
            } else {
                "Black holes".into()
            };
        }
        return;
    }
    let points = profile(view.time).expect("bridge controls maintain the supported time domain");
    for mut text in &mut status {
        **text = format!(
            "Einstein-Rosen bridge | Kruskal v={:+.2} | throat={:.3} r_g\nEquatorial spatial embedding; nontraversable. |v| <= 0.95; singular pinch at |v|=1 excluded.",
            view.time, points[0][0],
        );
    }
    for sign in [-1.0_f32, 1.0] {
        let color = if sign > 0.0 {
            Color::srgb(0.3, 0.65, 1.0)
        } else {
            Color::srgb(1.0, 0.6, 0.25)
        };
        let vertex = |p: [f64; 2], angle: f32| {
            Vec3::new(
                p[0] as f32 * angle.cos(),
                sign * p[1] as f32,
                p[0] as f32 * angle.sin(),
            )
        };
        for j in 0..24 {
            let angle = std::f32::consts::TAU * j as f32 / 24.0;
            gizmos.linestrip(points.iter().map(|&p| vertex(p, angle)), color);
        }
        for &point in points.iter().step_by(4) {
            gizmos.linestrip(
                (0..=96).map(|j| vertex(point, std::f32::consts::TAU * j as f32 / 96.0)),
                color,
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "requires a GPU; renders the complete bridge scene offscreen"]
    fn bridge_scene_renders_and_switches_back() {
        use bevy::{
            camera::RenderTarget,
            render::{
                RenderPlugin,
                gpu_readback::{Readback, ReadbackComplete},
                render_resource::{Extent3d, TextureFormat, TextureUsages},
            },
            window::ExitCondition,
            winit::WinitPlugin,
        };
        #[derive(Resource, Default)]
        struct Pixels(Vec<u8>);
        let save_scene = |app: &App, path: &str| {
            // WGPU aligns each 3200-byte image row to 256 bytes for readback.
            const PADDED_ROW_BYTES: usize = 3328;
            let pixels: Vec<u8> = app
                .world()
                .resource::<Pixels>()
                .0
                .as_chunks::<PADDED_ROW_BYTES>()
                .0
                .iter()
                .flat_map(|row| &row[..800 * 4])
                .copied()
                .collect();
            assert_eq!(pixels.len(), 800 * 600 * 4);
            Image::new(
                Extent3d {
                    width: 800,
                    height: 600,
                    depth_or_array_layers: 1,
                },
                bevy::render::render_resource::TextureDimension::D2,
                pixels.clone(),
                TextureFormat::Rgba8UnormSrgb,
                bevy::asset::RenderAssetUsages::MAIN_WORLD,
            )
            .try_into_dynamic()
            .unwrap()
            .save(path)
            .unwrap();
            pixels
        };
        let mut app = App::new();
        app.add_plugins(
            DefaultPlugins
                .set(WindowPlugin {
                    primary_window: None,
                    exit_condition: ExitCondition::DontExit,
                    ..default()
                })
                .set(RenderPlugin {
                    synchronous_pipeline_compilation: true,
                    ..default()
                })
                .disable::<bevy::gilrs::GilrsPlugin>()
                .disable::<WinitPlugin>()
                .disable::<bevy::render::pipelined_rendering::PipelinedRenderingPlugin>(),
        )
        .init_resource::<Pixels>()
        .add_plugins((
            crate::camera::OrbitalCameraPlugin,
            crate::simulation::SimulationPlugin,
            BridgePlugin,
            crate::grid::GridPlugin,
            crate::compute::GeodesicComputePlugin,
            crate::swarm::SwarmPlugin,
            crate::ui::UiPlugin,
        ))
        .add_systems(
            PostStartup,
            |mut commands: Commands,
             mut images: ResMut<Assets<Image>>,
             cameras: Query<(Entity, Has<crate::camera::PerspectiveCamera>), With<Camera>>| {
                let mut image =
                    Image::new_target_texture(800, 600, TextureFormat::Rgba8UnormSrgb, None);
                image.texture_descriptor.usage |= TextureUsages::COPY_SRC;
                let output = images.add(image);
                for (camera, perspective) in &cameras {
                    commands
                        .entity(camera)
                        .insert(RenderTarget::Image(output.clone().into()));
                    if perspective {
                        commands.entity(camera).insert(IsDefaultUiCamera);
                    }
                }
                commands.spawn(Readback::texture(output)).observe(
                    |event: On<ReadbackComplete>, mut pixels: ResMut<Pixels>| {
                        pixels.0 = event.data.clone();
                    },
                );
            },
        );
        while app.plugins_state() != bevy::app::PluginsState::Ready {
            bevy::tasks::tick_global_task_pools_on_main_thread();
        }
        app.finish();
        app.cleanup();
        app.update();
        app.world_mut()
            .resource_scope(|world, mut view: Mut<BridgeView>| {
                apply_action(
                    &mut view,
                    &mut world.resource_mut::<OrbitalCamera>(),
                    BridgeAction::Toggle,
                );
                view.matter_playing = false;
                view.matter_time = 0.0;
            });
        let (near_sky, far_sky) = {
            let mut skies = app.world_mut().resource_mut::<crate::compute::SkyboxSet>();
            skies.current = 1;
            (skies.handles[1].clone(), skies.handles[2].clone())
        };
        app.world_mut()
            .resource_mut::<crate::compute::SkyboxImage>()
            .0 = near_sky.clone();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(45);
        while app
            .world()
            .resource::<crate::compute::SkyboxData>()
            .handle
            .as_ref()
            != Some(&near_sky)
            || app
                .world()
                .resource::<crate::compute::OtherSkyboxData>()
                .0
                .handle
                .as_ref()
                != Some(&far_sky)
        {
            app.update();
            assert!(
                std::time::Instant::now() < deadline,
                "second celestial sky did not load"
            );
        }
        for _ in 0..20 {
            app.update();
        }
        assert!(
            app.world().resource::<crate::compute::RenderFrameCount>().0 > 0,
            "inactive binary motion must not reset wormhole temporal accumulation"
        );
        assert_eq!(
            app.world()
                .resource::<crate::compute::CameraUniform>()
                .wormhole_radius,
            black_hole::ellis::THROAT_RADIUS
        );
        let initial = save_scene(&app, "target/wormhole-smoke.png");
        app.world_mut().resource_mut::<BridgeView>().matter_time = 28.0;
        app.update();
        assert_eq!(
            app.world().resource::<crate::compute::RenderFrameCount>().0,
            0
        );
        for _ in 0..20 {
            app.update();
        }
        let evolved = save_scene(&app, "target/wormhole-matter-throat.png");
        assert!(
            initial
                .iter()
                .zip(&evolved)
                .take(800 * 500 * 4)
                .filter(|(a, b)| a.abs_diff(**b) > 4)
                .count()
                > 2000,
            "evolving dust must change the rendered scene above the control panel"
        );
        app.world_mut().resource_mut::<BridgeView>().matter_playing = true;
        app.update();
        assert!(app.world().resource::<BridgeView>().matter_time > 28.0);
        assert_eq!(
            app.world().resource::<crate::compute::RenderFrameCount>().0,
            0
        );
        app.world_mut().resource_mut::<BridgeView>().matter_playing = false;
        app.world_mut()
            .resource_scope(|world, mut view: Mut<BridgeView>| {
                apply_action(
                    &mut view,
                    &mut world.resource_mut::<OrbitalCamera>(),
                    BridgeAction::Toggle,
                );
            });
        // Exercise the actual input system through widget presses, just as the UI does.
        let button = app
            .world_mut()
            .spawn((Button, BridgeAction::Later, Pressed))
            .id();
        for _ in 0..15 {
            app.update();
        }
        app.world_mut().entity_mut(button).despawn();
        assert_eq!(app.world().resource::<BridgeView>().time, 0.05);
        let world = app.world_mut();
        let mut panels = world.query_filtered::<&Node, With<BlackHoleControls>>();
        assert_eq!(panels.iter(world).count(), 2);
        assert!(panels.iter(world).all(|node| node.display == Display::None));
        assert!(
            world
                .query::<(&Sprite, &Visibility)>()
                .iter(world)
                .all(|(_, visibility)| *visibility == Visibility::Hidden)
        );
        let pixels = save_scene(&app, "target/bridge-smoke.png");
        assert!(
            pixels
                .as_chunks::<4>()
                .0
                .iter()
                .filter(|p| p[2] > 100 && p[2] > p[0])
                .count()
                > 500,
            "blue sheet is visible"
        );
        let play = app
            .world_mut()
            .spawn((Button, BridgeAction::Play, Pressed))
            .id();
        app.update();
        app.world_mut().entity_mut(play).despawn();
        assert!(app.world().resource::<BridgeView>().playing);
        assert!(app.world().resource::<BridgeView>().time > 0.05);
        app.world_mut().resource_mut::<BridgeView>().time = MAX_TIME;
        app.update();
        assert!(!app.world().resource::<BridgeView>().playing);
        app.world_mut()
            .resource_scope(|world, mut view: Mut<BridgeView>| {
                apply_action(
                    &mut view,
                    &mut world.resource_mut::<OrbitalCamera>(),
                    BridgeAction::Toggle,
                );
            });
        for _ in 0..5 {
            app.update();
        }
        let world = app.world_mut();
        assert!(
            world
                .query_filtered::<&Node, With<BlackHoleControls>>()
                .iter(world)
                .all(|node| node.display == Display::Flex)
        );
        assert!(
            world
                .query::<(&Sprite, &Visibility)>()
                .iter(world)
                .all(|(_, visibility)| *visibility == Visibility::Visible)
        );
    }

    #[test]
    fn switching_preserves_black_hole_camera_and_resets_accumulation() {
        let mut view = BridgeView::default();
        let mut cam = OrbitalCamera {
            radius: 70.0,
            elevation: 2.0,
            min_radius: 3.0,
            ..default()
        };
        let original = [cam.radius, cam.elevation, cam.min_radius];
        apply_action(&mut view, &mut cam, BridgeAction::Toggle);
        assert_eq!(view.mode, SimulationView::Ellis);
        assert!(cam.is_moving);
        assert_eq!(cam.radius, 12.0);
        apply_action(&mut view, &mut cam, BridgeAction::Toggle);
        assert_eq!(view.mode, SimulationView::EinsteinRosen);
        assert_eq!(cam.radius, 48.0);
        apply_action(&mut view, &mut cam, BridgeAction::Toggle);
        assert_eq!(view.mode, SimulationView::BlackHoles);
        assert!(cam.is_moving);
        assert_eq!([cam.radius, cam.elevation, cam.min_radius], original);
    }

    #[test]
    fn time_actions_clamp_pause_reset_and_ignore_the_black_hole_view() {
        let mut view = BridgeView::default();
        let mut cam = OrbitalCamera::default();
        apply_action(&mut view, &mut cam, BridgeAction::Later);
        assert_eq!(view.time, 0.0);
        apply_action(&mut view, &mut cam, BridgeAction::Toggle);
        apply_action(&mut view, &mut cam, BridgeAction::Toggle);
        for _ in 0..50 {
            apply_action(&mut view, &mut cam, BridgeAction::Later);
        }
        assert_eq!(view.time, MAX_TIME);
        apply_action(&mut view, &mut cam, BridgeAction::Play);
        assert_eq!(view.time, -MAX_TIME);
        assert!(view.playing);
        apply_action(&mut view, &mut cam, BridgeAction::Earlier);
        assert_eq!(view.time, -MAX_TIME);
        assert!(!view.playing);
        apply_action(&mut view, &mut cam, BridgeAction::Reset);
        assert_eq!(view.time, 0.0);
    }

    #[test]
    fn matter_clock_uses_elapsed_time_and_stops_when_inactive() {
        use bevy::time::TimeUpdateStrategy;
        use std::time::Duration;
        for fps in [30, 60, 120] {
            let mut app = App::new();
            app.add_plugins(MinimalPlugins)
                .init_resource::<BridgeView>()
                .init_resource::<OrbitalCamera>()
                .init_resource::<ButtonInput<KeyCode>>()
                .insert_resource(TimeUpdateStrategy::ManualDuration(Duration::ZERO))
                .add_systems(Update, update_controls);
            app.world_mut().resource_mut::<BridgeView>().mode = SimulationView::Ellis;
            app.update();
            let mut elapsed = Duration::ZERO;
            for frame in 1..=4 * fps {
                let next = Duration::from_secs_f64(frame as f64 / fps as f64);
                app.insert_resource(TimeUpdateStrategy::ManualDuration(next - elapsed));
                app.update();
                elapsed = next;
            }
            assert!((app.world().resource::<BridgeView>().matter_time - 4.0).abs() < 1e-9);
            app.world_mut().resource_mut::<BridgeView>().matter_playing = false;
            app.world_mut().resource_mut::<OrbitalCamera>().is_moving = false;
            app.update();
            assert!(!app.world().resource::<OrbitalCamera>().is_moving);
            assert!((app.world().resource::<BridgeView>().matter_time - 4.0).abs() < 1e-9);
            app.world_mut().resource_mut::<BridgeView>().matter_playing = true;
            app.world_mut().resource_mut::<BridgeView>().matter_enabled = false;
            app.update();
            assert!((app.world().resource::<BridgeView>().matter_time - 4.0).abs() < 1e-9);
            app.world_mut().resource_mut::<BridgeView>().matter_enabled = true;
            app.world_mut().resource_mut::<BridgeView>().mode = SimulationView::BlackHoles;
            app.update();
            assert!((app.world().resource::<BridgeView>().matter_time - 4.0).abs() < 1e-9);
        }
    }

    #[test]
    fn matter_actions_pause_toggle_and_rewind_with_accumulation_resets() {
        let mut view = BridgeView {
            mode: SimulationView::Ellis,
            matter_time: 28.0,
            ..default()
        };
        let mut cam = OrbitalCamera::default();
        apply_action(&mut view, &mut cam, BridgeAction::Play);
        assert!(!view.matter_playing && cam.is_moving);
        apply_action(&mut view, &mut cam, BridgeAction::Reset);
        assert_eq!(view.matter_time, 0.0);
        apply_action(&mut view, &mut cam, BridgeAction::ToggleMatter);
        assert!(!view.matter_enabled);
        apply_action(&mut view, &mut cam, BridgeAction::Play);
        assert!(!view.matter_playing);
    }
}
