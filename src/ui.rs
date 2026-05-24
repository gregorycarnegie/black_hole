use bevy::prelude::*;

use crate::{
    camera::{OrbitalCamera, ITER_PRESETS},
    compute::{RenderScale, SkyboxImage, SkyboxSet, SCALE_PRESETS, SKYBOX_NAMES},
    grid::GridVisible,
    simulation::{
        DiskConfig, DebugBodiesEnabled, GravityEnabled, SimObjects, kerr_horizon_radius,
        scene_objects,
    },
};

pub struct UiPlugin;

impl Plugin for UiPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(Startup, setup_panel).add_systems(
            Update,
            (
                handle_button_press,
                step_button_colors,
                update_value_displays,
                update_toggle_buttons,
            ),
        );
    }
}

// ── Action tag on every button ───────────────────────────────────────────────

#[derive(Component, Clone, Copy, PartialEq)]
enum UiAction {
    SpinDown,
    SpinUp,
    DiskRadiusDown,
    DiskRadiusUp,
    MaxIterDown,
    MaxIterUp,
    FovDown,
    FovUp,
    RenderScaleDown,
    RenderScaleUp,
    SkyboxPrev,
    SkyboxNext,
    DiskModelPrev,
    DiskModelNext,
    ToggleGrid,
    ToggleGravity,
    ToggleHeatmap,
    ToggleDebugBodies,
}

/// Marks a Text node whose content mirrors a live value.
#[derive(Component, Clone, Copy, PartialEq)]
enum ValueDisplay {
    Spin,
    DiskRadius,
    MaxIter,
    Fov,
    RenderScale,
    Skybox,
    DiskModel,
}

/// Marks a toggle button so its background colour tracks on/off state.
#[derive(Component, Clone, Copy, PartialEq)]
enum ToggleLabel {
    Grid,
    Gravity,
    Heatmap,
    DebugBodies,
}

// ── Palette ──────────────────────────────────────────────────────────────────

const PANEL_BG: Color = Color::srgba(0.05, 0.05, 0.08, 0.90);
const LABEL_COLOR: Color = Color::srgb(0.60, 0.62, 0.72);
const VALUE_COLOR: Color = Color::WHITE;
const HEADER_COLOR: Color = Color::srgb(0.75, 0.76, 0.88);
const BTN_NORMAL: Color = Color::srgb(0.18, 0.18, 0.26);
const BTN_HOVER: Color = Color::srgb(0.28, 0.28, 0.40);
const TOGGLE_ON: Color = Color::srgb(0.10, 0.46, 0.22);
const TOGGLE_ON_HOVER: Color = Color::srgb(0.14, 0.58, 0.30);
const TOGGLE_OFF: Color = Color::srgb(0.26, 0.10, 0.10);
const TOGGLE_OFF_HOVER: Color = Color::srgb(0.38, 0.15, 0.15);
const SEP_COLOR: Color = Color::srgba(0.35, 0.36, 0.48, 0.55);

// ── Panel setup ──────────────────────────────────────────────────────────────

fn setup_panel(mut commands: Commands) {
    commands
        .spawn((
            Node {
                position_type: PositionType::Absolute,
                top: Val::Px(8.0),
                right: Val::Px(8.0),
                flex_direction: FlexDirection::Column,
                padding: UiRect::all(Val::Px(10.0)),
                row_gap: Val::Px(5.0),
                min_width: Val::Px(248.0),
                ..default()
            },
            BackgroundColor(PANEL_BG),
        ))
        .with_children(|root| {
            root.spawn((
                Text::new("CONTROLS"),
                TextFont { font_size: 11.0, ..default() },
                TextColor(HEADER_COLOR),
            ));

            spawn_sep(root);

            spawn_step_row(root, "Spin a*", UiAction::SpinDown, UiAction::SpinUp, ValueDisplay::Spin);
            spawn_step_row(root, "Outer R", UiAction::DiskRadiusDown, UiAction::DiskRadiusUp, ValueDisplay::DiskRadius);
            spawn_step_row(root, "Iterations", UiAction::MaxIterDown, UiAction::MaxIterUp, ValueDisplay::MaxIter);
            spawn_step_row(root, "FOV", UiAction::FovDown, UiAction::FovUp, ValueDisplay::Fov);
            spawn_step_row(root, "Render %", UiAction::RenderScaleDown, UiAction::RenderScaleUp, ValueDisplay::RenderScale);

            spawn_sep(root);

            spawn_cycle_row(root, "Skybox", UiAction::SkyboxPrev, UiAction::SkyboxNext, ValueDisplay::Skybox);
            spawn_cycle_row(root, "Disk", UiAction::DiskModelPrev, UiAction::DiskModelNext, ValueDisplay::DiskModel);

            spawn_sep(root);

            spawn_toggle_row(root, &[
                ("Grid", UiAction::ToggleGrid, ToggleLabel::Grid),
                ("Gravity", UiAction::ToggleGravity, ToggleLabel::Gravity),
            ]);
            spawn_toggle_row(root, &[
                ("Heatmap", UiAction::ToggleHeatmap, ToggleLabel::Heatmap),
                ("Debug", UiAction::ToggleDebugBodies, ToggleLabel::DebugBodies),
            ]);
        });
}

fn spawn_sep(parent: &mut ChildSpawnerCommands) {
    parent.spawn((
        Node { height: Val::Px(1.0), width: Val::Percent(100.0), ..default() },
        BackgroundColor(SEP_COLOR),
    ));
}

fn spawn_step_row(
    parent: &mut ChildSpawnerCommands,
    label: &str,
    down: UiAction,
    up: UiAction,
    display: ValueDisplay,
) {
    parent
        .spawn(Node {
            flex_direction: FlexDirection::Row,
            align_items: AlignItems::Center,
            column_gap: Val::Px(4.0),
            ..default()
        })
        .with_children(|row| {
            row.spawn((
                Node { min_width: Val::Px(72.0), ..default() },
                Text::new(label),
                TextFont { font_size: 11.0, ..default() },
                TextColor(LABEL_COLOR),
            ));
            spawn_arrow_btn(row, "<", down);
            row.spawn((
                Node { min_width: Val::Px(58.0), justify_content: JustifyContent::Center, ..default() },
                Text::new("--"),
                TextFont { font_size: 11.0, ..default() },
                TextColor(VALUE_COLOR),
                display,
            ));
            spawn_arrow_btn(row, ">", up);
        });
}

fn spawn_cycle_row(
    parent: &mut ChildSpawnerCommands,
    label: &str,
    prev: UiAction,
    next: UiAction,
    display: ValueDisplay,
) {
    parent
        .spawn(Node {
            flex_direction: FlexDirection::Row,
            align_items: AlignItems::Center,
            column_gap: Val::Px(4.0),
            ..default()
        })
        .with_children(|row| {
            row.spawn((
                Node { min_width: Val::Px(72.0), ..default() },
                Text::new(label),
                TextFont { font_size: 11.0, ..default() },
                TextColor(LABEL_COLOR),
            ));
            spawn_arrow_btn(row, "<", prev);
            row.spawn((
                Node {
                    flex_grow: 1.0,
                    justify_content: JustifyContent::Center,
                    ..default()
                },
                Text::new("--"),
                TextFont { font_size: 10.0, ..default() },
                TextColor(VALUE_COLOR),
                display,
            ));
            spawn_arrow_btn(row, ">", next);
        });
}

fn spawn_arrow_btn(parent: &mut ChildSpawnerCommands, symbol: &str, action: UiAction) {
    parent
        .spawn((
            Button,
            Node {
                width: Val::Px(22.0),
                height: Val::Px(20.0),
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                ..default()
            },
            BackgroundColor(BTN_NORMAL),
            action,
        ))
        .with_children(|b| {
            b.spawn((
                Text::new(symbol),
                TextFont { font_size: 11.0, ..default() },
                TextColor(Color::WHITE),
            ));
        });
}

fn spawn_toggle_row(
    parent: &mut ChildSpawnerCommands,
    toggles: &[(&str, UiAction, ToggleLabel)],
) {
    parent
        .spawn(Node {
            flex_direction: FlexDirection::Row,
            column_gap: Val::Px(4.0),
            ..default()
        })
        .with_children(|row| {
            for (label, action, toggle_label) in toggles {
                row.spawn((
                    Button,
                    Node {
                        flex_grow: 1.0,
                        height: Val::Px(22.0),
                        justify_content: JustifyContent::Center,
                        align_items: AlignItems::Center,
                        ..default()
                    },
                    BackgroundColor(TOGGLE_OFF),
                    *action,
                    *toggle_label,
                ))
                .with_children(|b| {
                    b.spawn((
                        Text::new(*label),
                        TextFont { font_size: 11.0, ..default() },
                        TextColor(Color::WHITE),
                    ));
                });
            }
        });
}

// ── Button press handler ─────────────────────────────────────────────────────

fn handle_button_press(
    query: Query<(&Interaction, &UiAction), (Changed<Interaction>, With<Button>)>,
    mut cam: ResMut<OrbitalCamera>,
    mut disk: ResMut<DiskConfig>,
    mut objects: ResMut<SimObjects>,
    mut grid: ResMut<GridVisible>,
    mut gravity: ResMut<GravityEnabled>,
    mut debug: ResMut<DebugBodiesEnabled>,
    mut scale: ResMut<RenderScale>,
    mut skybox_set: ResMut<SkyboxSet>,
    mut skybox_active: ResMut<SkyboxImage>,
) {
    for (interaction, action) in &query {
        if *interaction != Interaction::Pressed {
            continue;
        }
        match action {
            UiAction::SpinDown => {
                disk.spin = (disk.spin - 0.05).clamp(-0.999, 0.999);
                sync_bh_radius(&disk, &mut objects);
                cam.is_moving = true;
            }
            UiAction::SpinUp => {
                disk.spin = (disk.spin + 0.05).clamp(-0.999, 0.999);
                sync_bh_radius(&disk, &mut objects);
                cam.is_moving = true;
            }
            UiAction::DiskRadiusDown => {
                disk.r_outer_rs = (disk.r_outer_rs - 1.0).max(4.0);
                cam.is_moving = true;
            }
            UiAction::DiskRadiusUp => {
                disk.r_outer_rs = (disk.r_outer_rs + 1.0).min(30.0);
                cam.is_moving = true;
            }
            UiAction::MaxIterDown => {
                let idx = iter_idx(cam.max_iter);
                if idx > 0 {
                    cam.max_iter = ITER_PRESETS[idx - 1];
                    cam.is_moving = true;
                }
            }
            UiAction::MaxIterUp => {
                let idx = iter_idx(cam.max_iter);
                if idx + 1 < ITER_PRESETS.len() {
                    cam.max_iter = ITER_PRESETS[idx + 1];
                    cam.is_moving = true;
                }
            }
            UiAction::FovDown => {
                cam.fov_degrees = (cam.fov_degrees - 5.0).clamp(10.0, 170.0);
                cam.is_moving = true;
            }
            UiAction::FovUp => {
                cam.fov_degrees = (cam.fov_degrees + 5.0).clamp(10.0, 170.0);
                cam.is_moving = true;
            }
            UiAction::RenderScaleDown => {
                let idx = scale_idx(scale.0);
                if idx > 0 {
                    scale.0 = SCALE_PRESETS[idx - 1];
                }
            }
            UiAction::RenderScaleUp => {
                let idx = scale_idx(scale.0);
                if idx + 1 < SCALE_PRESETS.len() {
                    scale.0 = SCALE_PRESETS[idx + 1];
                }
            }
            UiAction::SkyboxPrev => {
                let n = skybox_set.handles.len();
                skybox_set.current = (skybox_set.current + n - 1) % n;
                skybox_active.0 = skybox_set.handles[skybox_set.current].clone();
                cam.is_moving = true;
            }
            UiAction::SkyboxNext => {
                let n = skybox_set.handles.len();
                skybox_set.current = (skybox_set.current + 1) % n;
                skybox_active.0 = skybox_set.handles[skybox_set.current].clone();
                cam.is_moving = true;
            }
            UiAction::DiskModelPrev => {
                let prev = disk.model.prev();
                let spin = disk.spin;
                *disk = DiskConfig::for_model(prev, spin);
                cam.is_moving = true;
            }
            UiAction::DiskModelNext => {
                let next = disk.model.next();
                let spin = disk.spin;
                *disk = DiskConfig::for_model(next, spin);
                cam.is_moving = true;
            }
            UiAction::ToggleGrid => {
                grid.0 = !grid.0;
            }
            UiAction::ToggleGravity => {
                gravity.0 = !gravity.0;
            }
            UiAction::ToggleHeatmap => {
                cam.debug_heatmap = !cam.debug_heatmap;
                cam.is_moving = true;
            }
            UiAction::ToggleDebugBodies => {
                debug.0 = !debug.0;
                let spin = disk.spin;
                objects.0 = scene_objects(spin, debug.0);
                cam.is_moving = true;
            }
        }
    }
}

fn sync_bh_radius(disk: &DiskConfig, objects: &mut SimObjects) {
    if let Some(bh) = objects.0.last_mut() {
        bh.radius = kerr_horizon_radius(disk.spin);
    }
}

fn iter_idx(max_iter: u32) -> usize {
    ITER_PRESETS
        .iter()
        .position(|&x| x == max_iter)
        .unwrap_or(ITER_PRESETS.len() - 1)
}

fn scale_idx(scale: f32) -> usize {
    SCALE_PRESETS
        .iter()
        .position(|&s| (s - scale).abs() < 0.01)
        .unwrap_or(1)
}

// ── Value display updater ────────────────────────────────────────────────────

fn update_value_displays(
    cam: Res<OrbitalCamera>,
    disk: Res<DiskConfig>,
    scale: Res<RenderScale>,
    skybox_set: Res<SkyboxSet>,
    mut query: Query<(&mut Text, &ValueDisplay)>,
) {
    for (mut text, display) in &mut query {
        **text = match display {
            ValueDisplay::Spin => format!("{:+.2}", disk.spin),
            ValueDisplay::DiskRadius => format!("{:.0} r_s", disk.r_outer_rs),
            ValueDisplay::MaxIter => format!("{}", cam.max_iter),
            ValueDisplay::Fov => format!("{:.0} deg", cam.fov_degrees),
            ValueDisplay::RenderScale => format!("{:.0}%", scale.0 * 100.0),
            ValueDisplay::Skybox => SKYBOX_NAMES[skybox_set.current].to_string(),
            ValueDisplay::DiskModel => disk.model.short_name().to_string(),
        };
    }
}

// ── Toggle button colour updater ─────────────────────────────────────────────

fn update_toggle_buttons(
    cam: Res<OrbitalCamera>,
    grid: Res<GridVisible>,
    gravity: Res<GravityEnabled>,
    debug: Res<DebugBodiesEnabled>,
    mut query: Query<(&Interaction, &mut BackgroundColor, &ToggleLabel)>,
) {
    for (interaction, mut bg, label) in &mut query {
        let active = match label {
            ToggleLabel::Grid => grid.0,
            ToggleLabel::Gravity => gravity.0,
            ToggleLabel::Heatmap => cam.debug_heatmap,
            ToggleLabel::DebugBodies => debug.0,
        };
        *bg = BackgroundColor(if *interaction == Interaction::Hovered {
            if active { TOGGLE_ON_HOVER } else { TOGGLE_OFF_HOVER }
        } else if active {
            TOGGLE_ON
        } else {
            TOGGLE_OFF
        });
    }
}

// ── Arrow button hover colours ───────────────────────────────────────────────

fn step_button_colors(
    mut query: Query<
        (&Interaction, &mut BackgroundColor),
        (Changed<Interaction>, With<UiAction>, Without<ToggleLabel>),
    >,
) {
    for (interaction, mut bg) in &mut query {
        *bg = BackgroundColor(match interaction {
            Interaction::Hovered => BTN_HOVER,
            _ => BTN_NORMAL,
        });
    }
}
