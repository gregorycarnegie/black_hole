use bevy::{
    ecs::system::SystemParam, picking::hover::Hovered, prelude::*, ui::Pressed, ui_widgets::Button,
};

use crate::{
    camera::{ITER_PRESETS, OrbitalCamera, POLARIZATION_VIEWS},
    compute::{RenderScale, SCALE_PRESETS, SKYBOX_NAMES, SkyboxImage, SkyboxSet},
    grid::GridVisible,
    simulation::{
        BINARY_AXIS_STEP, BINARY_SPIN_STEP, BinaryBlackHoles, DebugBodiesEnabled, DiskConfig,
        GravityEnabled, SimObjects, scene_objects,
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

#[derive(Component, Clone, Copy, Debug, PartialEq)]
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
    BinaryHolePrev,
    BinaryHoleNext,
    BinaryAxisXDown,
    BinaryAxisXUp,
    BinaryAxisYDown,
    BinaryAxisYUp,
    BinaryAxisZDown,
    BinaryAxisZUp,
    PolarizationPrev,
    PolarizationNext,
    FrequencyDown,
    FrequencyUp,
    FaradayDown,
    FaradayUp,
    ConversionDown,
    ConversionUp,
    ToggleGrid,
    ToggleGravity,
    ToggleHeatmap,
    ToggleBinary,
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
    Polarization,
    Frequency,
    Faraday,
    Conversion,
    BinaryHole,
    BinaryAxisX,
    BinaryAxisY,
    BinaryAxisZ,
}

/// Marks a toggle button so its background colour tracks on/off state.
#[derive(Component, Clone, Copy, PartialEq)]
enum ToggleLabel {
    Grid,
    Gravity,
    Heatmap,
    Binary,
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

type UiButtonInteractionQuery<'w, 's> =
    Query<'w, 's, &'static UiAction, (Added<Pressed>, With<Button>)>;

type StepButtonColorQuery<'w, 's> = Query<
    'w,
    's,
    (&'static Hovered, &'static mut BackgroundColor),
    (Changed<Hovered>, With<UiAction>, Without<ToggleLabel>),
>;

#[derive(SystemParam)]
struct ButtonPressParams<'w> {
    cam: ResMut<'w, OrbitalCamera>,
    disk: ResMut<'w, DiskConfig>,
    objects: ResMut<'w, SimObjects>,
    grid: ResMut<'w, GridVisible>,
    gravity: ResMut<'w, GravityEnabled>,
    debug: ResMut<'w, DebugBodiesEnabled>,
    binary: ResMut<'w, BinaryBlackHoles>,
    scale: ResMut<'w, RenderScale>,
    skybox_set: ResMut<'w, SkyboxSet>,
    skybox_active: ResMut<'w, SkyboxImage>,
}

// ── Panel setup ──────────────────────────────────────────────────────────────

#[cfg_attr(test, mutants::skip)] // layout only
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
                TextFont {
                    font_size: FontSize::Px(11.0),
                    ..default()
                },
                TextColor(HEADER_COLOR),
            ));

            spawn_sep(root);

            spawn_step_row(
                root,
                "Spin a*",
                UiAction::SpinDown,
                UiAction::SpinUp,
                ValueDisplay::Spin,
            );
            spawn_step_row(
                root,
                "Outer R",
                UiAction::DiskRadiusDown,
                UiAction::DiskRadiusUp,
                ValueDisplay::DiskRadius,
            );
            spawn_step_row(
                root,
                "Iterations",
                UiAction::MaxIterDown,
                UiAction::MaxIterUp,
                ValueDisplay::MaxIter,
            );
            spawn_step_row(
                root,
                "FOV",
                UiAction::FovDown,
                UiAction::FovUp,
                ValueDisplay::Fov,
            );
            spawn_step_row(
                root,
                "Render %",
                UiAction::RenderScaleDown,
                UiAction::RenderScaleUp,
                ValueDisplay::RenderScale,
            );

            spawn_sep(root);

            spawn_cycle_row(
                root,
                "Skybox",
                UiAction::SkyboxPrev,
                UiAction::SkyboxNext,
                ValueDisplay::Skybox,
            );
            spawn_cycle_row(
                root,
                "Disk",
                UiAction::DiskModelPrev,
                UiAction::DiskModelNext,
                ValueDisplay::DiskModel,
            );

            spawn_sep(root);

            spawn_cycle_row(
                root,
                "BH",
                UiAction::BinaryHolePrev,
                UiAction::BinaryHoleNext,
                ValueDisplay::BinaryHole,
            );
            spawn_step_row(
                root,
                "Axis X",
                UiAction::BinaryAxisXDown,
                UiAction::BinaryAxisXUp,
                ValueDisplay::BinaryAxisX,
            );
            spawn_step_row(
                root,
                "Axis Y",
                UiAction::BinaryAxisYDown,
                UiAction::BinaryAxisYUp,
                ValueDisplay::BinaryAxisY,
            );
            spawn_step_row(
                root,
                "Axis Z",
                UiAction::BinaryAxisZDown,
                UiAction::BinaryAxisZUp,
                ValueDisplay::BinaryAxisZ,
            );

            spawn_sep(root);

            spawn_toggle_row(
                root,
                &[
                    ("Grid", UiAction::ToggleGrid, ToggleLabel::Grid),
                    ("Binary", UiAction::ToggleBinary, ToggleLabel::Binary),
                ],
            );
            spawn_toggle_row(
                root,
                &[
                    ("Gravity", UiAction::ToggleGravity, ToggleLabel::Gravity),
                    ("Heatmap", UiAction::ToggleHeatmap, ToggleLabel::Heatmap),
                ],
            );
            spawn_toggle_row(
                root,
                &[(
                    "Debug",
                    UiAction::ToggleDebugBodies,
                    ToggleLabel::DebugBodies,
                )],
            );
        });
    commands
        .spawn((
            Node {
                position_type: PositionType::Absolute,
                top: Val::Px(48.0),
                left: Val::Px(8.0),
                flex_direction: FlexDirection::Column,
                padding: UiRect::all(Val::Px(10.0)),
                row_gap: Val::Px(5.0),
                min_width: Val::Px(248.0),
                ..default()
            },
            BackgroundColor(PANEL_BG),
        ))
        .with_children(|root| {
            spawn_cycle_row(
                root,
                "Stokes",
                UiAction::PolarizationPrev,
                UiAction::PolarizationNext,
                ValueDisplay::Polarization,
            );
            spawn_step_row(
                root,
                "GHz",
                UiAction::FrequencyDown,
                UiAction::FrequencyUp,
                ValueDisplay::Frequency,
            );
            spawn_step_row(
                root,
                "Faraday",
                UiAction::FaradayDown,
                UiAction::FaradayUp,
                ValueDisplay::Faraday,
            );
            spawn_step_row(
                root,
                "Convert",
                UiAction::ConversionDown,
                UiAction::ConversionUp,
                ValueDisplay::Conversion,
            );
            spawn_sep(root);

            root.spawn((
                Text::new("P: cycle view | M: hot flow"),
                TextFont {
                    font_size: FontSize::Px(11.0),
                    ..default()
                },
                TextColor(LABEL_COLOR),
            ));
        });
}

#[cfg_attr(test, mutants::skip)] // layout only
fn spawn_sep(parent: &mut ChildSpawnerCommands) {
    parent.spawn((
        Node {
            height: Val::Px(1.0),
            width: Val::Percent(100.0),
            ..default()
        },
        BackgroundColor(SEP_COLOR),
    ));
}

#[cfg_attr(test, mutants::skip)] // layout only
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
                Node {
                    min_width: Val::Px(72.0),
                    ..default()
                },
                Text::new(label),
                TextFont {
                    font_size: FontSize::Px(11.0),
                    ..default()
                },
                TextColor(LABEL_COLOR),
            ));
            spawn_arrow_btn(row, "<", down);
            row.spawn((
                Node {
                    min_width: Val::Px(58.0),
                    justify_content: JustifyContent::Center,
                    ..default()
                },
                Text::new("--"),
                TextFont {
                    font_size: FontSize::Px(11.0),
                    ..default()
                },
                TextColor(VALUE_COLOR),
                display,
            ));
            spawn_arrow_btn(row, ">", up);
        });
}

#[cfg_attr(test, mutants::skip)] // layout only
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
                Node {
                    min_width: Val::Px(72.0),
                    ..default()
                },
                Text::new(label),
                TextFont {
                    font_size: FontSize::Px(11.0),
                    ..default()
                },
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
                TextFont {
                    font_size: FontSize::Px(10.0),
                    ..default()
                },
                TextColor(VALUE_COLOR),
                display,
            ));
            spawn_arrow_btn(row, ">", next);
        });
}

#[cfg_attr(test, mutants::skip)] // layout only
fn spawn_arrow_btn(parent: &mut ChildSpawnerCommands, symbol: &str, action: UiAction) {
    parent
        .spawn((
            Button,
            Hovered::default(),
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
                TextFont {
                    font_size: FontSize::Px(11.0),
                    ..default()
                },
                TextColor(Color::WHITE),
            ));
        });
}

#[cfg_attr(test, mutants::skip)] // layout only
fn spawn_toggle_row(parent: &mut ChildSpawnerCommands, toggles: &[(&str, UiAction, ToggleLabel)]) {
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
                    Hovered::default(),
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
                        TextFont {
                            font_size: FontSize::Px(11.0),
                            ..default()
                        },
                        TextColor(Color::WHITE),
                    ));
                });
            }
        });
}

// ── Button press handler ─────────────────────────────────────────────────────

fn handle_button_press(query: UiButtonInteractionQuery<'_, '_>, mut params: ButtonPressParams) {
    for action in &query {
        match action {
            UiAction::SpinDown => {
                if params.binary.enabled {
                    params.binary.adjust_selected_magnitude(-BINARY_SPIN_STEP);
                } else {
                    params.disk.spin = (params.disk.spin - 0.05).clamp(-0.999, 0.999);
                }
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::SpinUp => {
                if params.binary.enabled {
                    params.binary.adjust_selected_magnitude(BINARY_SPIN_STEP);
                } else {
                    params.disk.spin = (params.disk.spin + 0.05).clamp(-0.999, 0.999);
                }
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::DiskRadiusDown => {
                params.disk.r_outer_rs = (params.disk.r_outer_rs - 1.0).max(4.0);
                params.cam.is_moving = true;
            }
            UiAction::DiskRadiusUp => {
                params.disk.r_outer_rs = (params.disk.r_outer_rs + 1.0).min(30.0);
                params.cam.is_moving = true;
            }
            UiAction::MaxIterDown => {
                let idx = iter_idx(params.cam.max_iter);
                if idx > 0 {
                    params.cam.max_iter = ITER_PRESETS[idx - 1];
                    params.cam.is_moving = true;
                }
            }
            UiAction::MaxIterUp => {
                let idx = iter_idx(params.cam.max_iter);
                if idx + 1 < ITER_PRESETS.len() {
                    params.cam.max_iter = ITER_PRESETS[idx + 1];
                    params.cam.is_moving = true;
                }
            }
            UiAction::FovDown => {
                params.cam.fov_degrees = (params.cam.fov_degrees - 5.0).clamp(10.0, 170.0);
                params.cam.is_moving = true;
            }
            UiAction::FovUp => {
                params.cam.fov_degrees = (params.cam.fov_degrees + 5.0).clamp(10.0, 170.0);
                params.cam.is_moving = true;
            }
            UiAction::RenderScaleDown => {
                let idx = scale_idx(params.scale.0);
                if idx > 0 {
                    params.scale.0 = SCALE_PRESETS[idx - 1];
                }
            }
            UiAction::RenderScaleUp => {
                let idx = scale_idx(params.scale.0);
                if idx + 1 < SCALE_PRESETS.len() {
                    params.scale.0 = SCALE_PRESETS[idx + 1];
                }
            }
            UiAction::SkyboxPrev => {
                let n = params.skybox_set.handles.len();
                params.skybox_set.current = (params.skybox_set.current + n - 1) % n;
                params.skybox_active.0 =
                    params.skybox_set.handles[params.skybox_set.current].clone();
                params.cam.is_moving = true;
            }
            UiAction::SkyboxNext => {
                let n = params.skybox_set.handles.len();
                params.skybox_set.current = (params.skybox_set.current + 1) % n;
                params.skybox_active.0 =
                    params.skybox_set.handles[params.skybox_set.current].clone();
                params.cam.is_moving = true;
            }
            UiAction::DiskModelPrev => {
                let prev = params.disk.model.prev();
                let spin = params.disk.spin;
                *params.disk = DiskConfig::for_model(prev, spin);
                params.cam.is_moving = true;
            }
            UiAction::DiskModelNext => {
                let next = params.disk.model.next();
                let spin = params.disk.spin;
                *params.disk = DiskConfig::for_model(next, spin);
                params.cam.is_moving = true;
            }
            UiAction::BinaryHolePrev => {
                params.binary.select_prev();
                params.cam.is_moving = true;
            }
            UiAction::BinaryHoleNext => {
                params.binary.select_next();
                params.cam.is_moving = true;
            }
            UiAction::BinaryAxisXDown => {
                params
                    .binary
                    .adjust_selected_axis_component(0, -BINARY_AXIS_STEP);
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::BinaryAxisXUp => {
                params
                    .binary
                    .adjust_selected_axis_component(0, BINARY_AXIS_STEP);
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::BinaryAxisYDown => {
                params
                    .binary
                    .adjust_selected_axis_component(1, -BINARY_AXIS_STEP);
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::BinaryAxisYUp => {
                params
                    .binary
                    .adjust_selected_axis_component(1, BINARY_AXIS_STEP);
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::BinaryAxisZDown => {
                params
                    .binary
                    .adjust_selected_axis_component(2, -BINARY_AXIS_STEP);
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::BinaryAxisZUp => {
                params
                    .binary
                    .adjust_selected_axis_component(2, BINARY_AXIS_STEP);
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::ToggleGrid => {
                params.grid.0 = !params.grid.0;
            }
            UiAction::ToggleGravity => {
                params.gravity.0 = !params.gravity.0;
            }
            UiAction::PolarizationPrev | UiAction::PolarizationNext => {
                let count = POLARIZATION_VIEWS.len() as u32;
                let step = if *action == UiAction::PolarizationNext {
                    1
                } else {
                    count - 1
                };
                params.cam.polarization_view = (params.cam.polarization_view + step) % count;
                params.cam.is_moving = true;
            }
            UiAction::FrequencyDown | UiAction::FrequencyUp => {
                let step = if *action == UiAction::FrequencyUp {
                    10.0
                } else {
                    -10.0
                };
                params.cam.frequency_ghz = (params.cam.frequency_ghz + step).clamp(30.0, 1000.0);
                params.cam.is_moving = true;
            }
            UiAction::FaradayDown | UiAction::FaradayUp => {
                let step = if *action == UiAction::FaradayUp {
                    0.25
                } else {
                    -0.25
                };
                params.cam.faraday_depth = (params.cam.faraday_depth + step).clamp(-20.0, 20.0);
                params.cam.is_moving = true;
            }
            UiAction::ConversionDown | UiAction::ConversionUp => {
                let step = if *action == UiAction::ConversionUp {
                    0.1
                } else {
                    -0.1
                };
                params.cam.conversion_depth = (params.cam.conversion_depth + step).clamp(0.0, 10.0);
                params.cam.is_moving = true;
            }
            UiAction::ToggleHeatmap => {
                params.cam.debug_heatmap = !params.cam.debug_heatmap;
                params.cam.is_moving = true;
            }
            UiAction::ToggleBinary => {
                params.binary.enabled = !params.binary.enabled;
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
            UiAction::ToggleDebugBodies => {
                params.debug.0 = !params.debug.0;
                rebuild_scene_objects(
                    &params.disk,
                    &params.debug,
                    &params.binary,
                    &mut params.objects,
                );
                params.cam.is_moving = true;
            }
        }
    }
}

fn rebuild_scene_objects(
    disk: &DiskConfig,
    debug: &DebugBodiesEnabled,
    binary: &BinaryBlackHoles,
    objects: &mut SimObjects,
) {
    objects.0 = scene_objects(
        disk.spin,
        debug.0,
        binary.enabled,
        binary.phase,
        binary.spins,
    );
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
    binary: Res<BinaryBlackHoles>,
    scale: Res<RenderScale>,
    skybox_set: Res<SkyboxSet>,
    mut query: Query<(&mut Text, &ValueDisplay)>,
) {
    for (mut text, display) in &mut query {
        **text = match display {
            ValueDisplay::Spin => {
                if binary.enabled {
                    format!("{:.2}", binary.selected_spin().magnitude)
                } else {
                    format!("{:+.2}", disk.spin)
                }
            }
            ValueDisplay::DiskRadius => format!("{:.0} r_s", disk.r_outer_rs),
            ValueDisplay::MaxIter => format!("{}", cam.max_iter),
            ValueDisplay::Fov => format!("{:.0} deg", cam.fov_degrees),
            ValueDisplay::RenderScale => format!("{:.0}%", scale.0 * 100.0),
            ValueDisplay::Skybox => SKYBOX_NAMES[skybox_set.current].to_string(),
            ValueDisplay::DiskModel => disk.model.short_name().to_string(),
            ValueDisplay::Polarization => {
                POLARIZATION_VIEWS[cam.polarization_view as usize].to_string()
            }
            ValueDisplay::Frequency => format!("{:.0}", cam.frequency_ghz),
            ValueDisplay::Faraday => format!("{:.2}", cam.faraday_depth),
            ValueDisplay::Conversion => format!("{:.1}", cam.conversion_depth),
            ValueDisplay::BinaryHole => binary.selected_label().to_string(),
            ValueDisplay::BinaryAxisX => format!("{:+.2}", binary.selected_spin().axis.x),
            ValueDisplay::BinaryAxisY => format!("{:+.2}", binary.selected_spin().axis.y),
            ValueDisplay::BinaryAxisZ => format!("{:+.2}", binary.selected_spin().axis.z),
        };
    }
}

// ── Toggle button colour updater ─────────────────────────────────────────────

fn update_toggle_buttons(
    cam: Res<OrbitalCamera>,
    grid: Res<GridVisible>,
    gravity: Res<GravityEnabled>,
    binary: Res<BinaryBlackHoles>,
    debug: Res<DebugBodiesEnabled>,
    mut query: Query<(&Hovered, &mut BackgroundColor, &ToggleLabel)>,
) {
    for (hovered, mut bg, label) in &mut query {
        let active = match label {
            ToggleLabel::Grid => grid.0,
            ToggleLabel::Gravity => gravity.0,
            ToggleLabel::Heatmap => cam.debug_heatmap,
            ToggleLabel::Binary => binary.enabled,
            ToggleLabel::DebugBodies => debug.0,
        };
        *bg = BackgroundColor(if hovered.get() {
            if active {
                TOGGLE_ON_HOVER
            } else {
                TOGGLE_OFF_HOVER
            }
        } else if active {
            TOGGLE_ON
        } else {
            TOGGLE_OFF
        });
    }
}

// ── Arrow button hover colours ───────────────────────────────────────────────

fn step_button_colors(mut query: StepButtonColorQuery<'_, '_>) {
    for (hovered, mut bg) in &mut query {
        *bg = BackgroundColor(if hovered.get() { BTN_HOVER } else { BTN_NORMAL });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulation::{BinarySpin, DiskModel};
    use proptest::prelude::*;
    use rstest::rstest;

    fn ui_app() -> App {
        let mut images = Assets::<Image>::default();
        let handles: Vec<_> = (0..SKYBOX_NAMES.len())
            .map(|_| images.add(Image::default()))
            .collect();
        let mut app = App::new();
        app.init_resource::<OrbitalCamera>()
            .init_resource::<DiskConfig>()
            .init_resource::<SimObjects>()
            .init_resource::<GridVisible>()
            .init_resource::<GravityEnabled>()
            .init_resource::<DebugBodiesEnabled>()
            .insert_resource(BinaryBlackHoles {
                enabled: false,
                ..default()
            })
            .init_resource::<RenderScale>()
            .insert_resource(SkyboxImage(handles[0].clone()))
            .insert_resource(SkyboxSet {
                handles,
                current: 0,
            })
            .add_systems(
                Update,
                (
                    handle_button_press,
                    update_value_displays,
                    update_toggle_buttons,
                ),
            );
        app
    }

    /// Presses a button carrying `action` for one frame.
    fn click(app: &mut App, action: UiAction) {
        app.world_mut().resource_mut::<OrbitalCamera>().is_moving = false;
        let button = app.world_mut().spawn((Button, action, Pressed)).id();
        app.update();
        app.world_mut().despawn(button);
    }

    fn cam(app: &App) -> &OrbitalCamera {
        app.world().resource::<OrbitalCamera>()
    }

    fn disk(app: &App) -> &DiskConfig {
        app.world().resource::<DiskConfig>()
    }

    fn binary(app: &App) -> &BinaryBlackHoles {
        app.world().resource::<BinaryBlackHoles>()
    }

    fn scene_len(app: &App) -> usize {
        app.world().resource::<SimObjects>().0.len()
    }

    /// A numeric value that a pair of panel buttons steps up and down.
    #[derive(Clone, Copy, Debug)]
    enum Field {
        Spin,
        Radius,
        Fov,
        Frequency,
        Faraday,
        Conversion,
        MaxIter,
        Scale,
        Polarization,
    }

    impl Field {
        fn get(self, app: &App) -> f64 {
            match self {
                Field::Spin => disk(app).spin as f64,
                Field::Radius => disk(app).r_outer_rs as f64,
                Field::Fov => cam(app).fov_degrees,
                Field::Frequency => cam(app).frequency_ghz as f64,
                Field::Faraday => cam(app).faraday_depth as f64,
                Field::Conversion => cam(app).conversion_depth as f64,
                Field::MaxIter => cam(app).max_iter as f64,
                Field::Scale => app.world().resource::<RenderScale>().0 as f64,
                Field::Polarization => cam(app).polarization_view as f64,
            }
        }

        fn set(self, app: &mut App, value: f64) {
            let world = app.world_mut();
            match self {
                Field::Spin => world.resource_mut::<DiskConfig>().spin = value as f32,
                Field::Radius => world.resource_mut::<DiskConfig>().r_outer_rs = value as f32,
                Field::Fov => world.resource_mut::<OrbitalCamera>().fov_degrees = value,
                Field::Frequency => {
                    world.resource_mut::<OrbitalCamera>().frequency_ghz = value as f32
                }
                Field::Faraday => {
                    world.resource_mut::<OrbitalCamera>().faraday_depth = value as f32
                }
                Field::Conversion => {
                    world.resource_mut::<OrbitalCamera>().conversion_depth = value as f32
                }
                Field::MaxIter => world.resource_mut::<OrbitalCamera>().max_iter = value as u32,
                Field::Scale => world.resource_mut::<RenderScale>().0 = value as f32,
                Field::Polarization => {
                    world.resource_mut::<OrbitalCamera>().polarization_view = value as u32
                }
            }
        }

        fn in_range(self, value: f64) -> bool {
            match self {
                // f32 fields compare as f32: 0.999_f32 widened to f64 exceeds 0.999_f64.
                Field::Spin => (-0.999..=0.999).contains(&(value as f32)),
                Field::Radius => (4.0..=30.0).contains(&(value as f32)),
                Field::Fov => (10.0..=170.0).contains(&value),
                Field::Frequency => (30.0..=1000.0).contains(&(value as f32)),
                Field::Faraday => (-20.0..=20.0).contains(&(value as f32)),
                Field::Conversion => (0.0..=10.0).contains(&(value as f32)),
                Field::MaxIter => ITER_PRESETS.contains(&(value as u32)),
                Field::Scale => SCALE_PRESETS.contains(&(value as f32)),
                Field::Polarization => value < POLARIZATION_VIEWS.len() as f64,
            }
        }
    }

    const STEP_BUTTONS: [(UiAction, Field); 18] = [
        (UiAction::SpinDown, Field::Spin),
        (UiAction::SpinUp, Field::Spin),
        (UiAction::DiskRadiusDown, Field::Radius),
        (UiAction::DiskRadiusUp, Field::Radius),
        (UiAction::FovDown, Field::Fov),
        (UiAction::FovUp, Field::Fov),
        (UiAction::FrequencyDown, Field::Frequency),
        (UiAction::FrequencyUp, Field::Frequency),
        (UiAction::FaradayDown, Field::Faraday),
        (UiAction::FaradayUp, Field::Faraday),
        (UiAction::ConversionDown, Field::Conversion),
        (UiAction::ConversionUp, Field::Conversion),
        (UiAction::MaxIterDown, Field::MaxIter),
        (UiAction::MaxIterUp, Field::MaxIter),
        (UiAction::RenderScaleDown, Field::Scale),
        (UiAction::RenderScaleUp, Field::Scale),
        (UiAction::PolarizationPrev, Field::Polarization),
        (UiAction::PolarizationNext, Field::Polarization),
    ];

    #[test]
    fn panel_buttons_are_widget_buttons_with_hover_tracking() {
        let mut app = App::new();
        app.add_systems(Startup, setup_panel);
        app.update();
        let world = app.world_mut();
        let mut buttons = world.query_filtered::<(Has<Button>, Has<Hovered>), With<UiAction>>();
        let found: Vec<_> = buttons.iter(world).collect();
        assert!(found.len() > 30, "only {} buttons", found.len());
        assert!(found.iter().all(|&(button, hovered)| button && hovered));
    }

    #[test]
    fn a_held_press_acts_once_and_only_on_buttons() {
        let mut app = ui_app();
        let button = app
            .world_mut()
            .spawn((Button, UiAction::DiskRadiusUp, Pressed))
            .id();
        app.update();
        app.update();
        assert_eq!(disk(&app).r_outer_rs, 16.0);

        let mut entity = app.world_mut().entity_mut(button);
        entity.remove::<(Button, Pressed)>();
        entity.insert(Pressed);
        app.update();
        assert_eq!(disk(&app).r_outer_rs, 16.0, "non-buttons are ignored");
    }

    #[rstest]
    #[case::spin_up(UiAction::SpinUp, Field::Spin, 0.82, 0.87, true)]
    #[case::spin_down(UiAction::SpinDown, Field::Spin, 0.999, 0.949, true)]
    #[case::spin_clamps_prograde(UiAction::SpinUp, Field::Spin, 0.97, 0.999, true)]
    #[case::spin_clamps_retrograde(UiAction::SpinDown, Field::Spin, -0.98, -0.999, true)]
    #[case::radius_down(UiAction::DiskRadiusDown, Field::Radius, 15.0, 14.0, true)]
    #[case::radius_up(UiAction::DiskRadiusUp, Field::Radius, 15.0, 16.0, true)]
    #[case::radius_clamps_inner(UiAction::DiskRadiusDown, Field::Radius, 4.5, 4.0, true)]
    #[case::radius_clamps_outer(UiAction::DiskRadiusUp, Field::Radius, 29.5, 30.0, true)]
    #[case::fov_up(UiAction::FovUp, Field::Fov, 60.0, 65.0, true)]
    #[case::fov_down(UiAction::FovDown, Field::Fov, 60.0, 55.0, true)]
    #[case::fov_clamps_wide(UiAction::FovUp, Field::Fov, 168.0, 170.0, true)]
    #[case::fov_clamps_narrow(UiAction::FovDown, Field::Fov, 12.0, 10.0, true)]
    #[case::frequency_down(UiAction::FrequencyDown, Field::Frequency, 230.0, 220.0, true)]
    #[case::frequency_up(UiAction::FrequencyUp, Field::Frequency, 230.0, 240.0, true)]
    #[case::frequency_clamps_high(UiAction::FrequencyUp, Field::Frequency, 995.0, 1000.0, true)]
    #[case::frequency_clamps_low(UiAction::FrequencyDown, Field::Frequency, 35.0, 30.0, true)]
    #[case::faraday_up(UiAction::FaradayUp, Field::Faraday, 1.0, 1.25, true)]
    #[case::faraday_down(UiAction::FaradayDown, Field::Faraday, 1.0, 0.75, true)]
    #[case::faraday_clamps_low(UiAction::FaradayDown, Field::Faraday, -19.9, -20.0, true)]
    #[case::faraday_clamps_high(UiAction::FaradayUp, Field::Faraday, 19.9, 20.0, true)]
    #[case::conversion_up(UiAction::ConversionUp, Field::Conversion, 0.3, 0.4, true)]
    #[case::conversion_down(UiAction::ConversionDown, Field::Conversion, 0.3, 0.2, true)]
    #[case::conversion_clamps_low(UiAction::ConversionDown, Field::Conversion, 0.05, 0.0, true)]
    #[case::conversion_clamps_high(UiAction::ConversionUp, Field::Conversion, 9.95, 10.0, true)]
    #[case::iterations_up(UiAction::MaxIterUp, Field::MaxIter, 10_000.0, 12_000.0, true)]
    #[case::iterations_down(UiAction::MaxIterDown, Field::MaxIter, 10_000.0, 8_000.0, true)]
    #[case::iterations_stop_at_bottom(
        UiAction::MaxIterDown,
        Field::MaxIter,
        8_000.0,
        8_000.0,
        false
    )]
    #[case::iterations_stop_at_top(UiAction::MaxIterUp, Field::MaxIter, 18_000.0, 18_000.0, false)]
    #[case::off_preset_iterations_count_as_top(
        UiAction::MaxIterDown,
        Field::MaxIter,
        12_345.0,
        16_000.0,
        true
    )]
    #[case::scale_down(UiAction::RenderScaleDown, Field::Scale, 0.5, 0.25, false)]
    #[case::scale_up(UiAction::RenderScaleUp, Field::Scale, 0.5, 0.75, false)]
    #[case::scale_stops_at_bottom(UiAction::RenderScaleDown, Field::Scale, 0.25, 0.25, false)]
    #[case::scale_stops_at_top(UiAction::RenderScaleUp, Field::Scale, 1.0, 1.0, false)]
    #[case::polarization_wraps_back(
        UiAction::PolarizationPrev,
        Field::Polarization,
        0.0,
        5.0,
        true
    )]
    #[case::polarization_wraps_forward(
        UiAction::PolarizationNext,
        Field::Polarization,
        5.0,
        0.0,
        true
    )]
    #[case::polarization_next(UiAction::PolarizationNext, Field::Polarization, 2.0, 3.0, true)]
    fn step_buttons_move_by_their_increments_and_clamp(
        #[case] action: UiAction,
        #[case] field: Field,
        #[case] start: f64,
        #[case] expected: f64,
        #[case] resets_accumulation: bool,
    ) {
        let mut app = ui_app();
        field.set(&mut app, start);
        click(&mut app, action);
        let actual = field.get(&app);
        assert!((actual - expected).abs() < 1e-5, "{actual} != {expected}");
        assert_eq!(cam(&app).is_moving, resets_accumulation);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(48))]

        #[test]
        fn no_button_sequence_leaves_a_parameter_out_of_range(
            presses in prop::collection::vec(prop::sample::select(STEP_BUTTONS.to_vec()), 1..60),
        ) {
            let mut app = ui_app();
            for (action, field) in presses {
                click(&mut app, action);
                let value = field.get(&app);
                prop_assert!(field.in_range(value), "{field:?} = {value} after {action:?}");
            }
        }
    }

    #[test]
    fn spin_buttons_rebuild_the_single_hole() {
        let mut app = ui_app();
        click(&mut app, UiAction::SpinUp);
        let objects = &app.world().resource::<SimObjects>().0;
        assert_eq!(objects.len(), 1);
        assert_eq!(objects[0].spin.y, disk(&app).spin);
    }

    #[test]
    fn spin_buttons_edit_the_selected_binary_hole() {
        let mut app = ui_app();
        {
            let mut binary = app.world_mut().resource_mut::<BinaryBlackHoles>();
            binary.enabled = true;
            binary.spins[1] = BinarySpin::new(0.5, Vec3::ONE);
        }
        click(&mut app, UiAction::BinaryHoleNext);
        assert_eq!(binary(&app).selected, 1);
        click(&mut app, UiAction::SpinDown);
        assert!((binary(&app).spins[1].magnitude - 0.45).abs() < 1e-6);
        click(&mut app, UiAction::SpinUp);
        click(&mut app, UiAction::SpinUp);
        assert!((binary(&app).spins[1].magnitude - 0.55).abs() < 1e-6);
        assert_eq!(disk(&app).spin, 0.82, "disk spin untouched");
        assert_eq!(scene_len(&app), 2);
        click(&mut app, UiAction::BinaryHolePrev);
        assert_eq!(binary(&app).selected, 0);
    }

    /// Starting from a (1,1,1) axis, each button moves only its own component.
    #[rstest]
    #[case(UiAction::BinaryAxisXUp, 0, 1.0)]
    #[case(UiAction::BinaryAxisXDown, 0, -1.0)]
    #[case(UiAction::BinaryAxisYUp, 1, 1.0)]
    #[case(UiAction::BinaryAxisYDown, 1, -1.0)]
    #[case(UiAction::BinaryAxisZUp, 2, 1.0)]
    #[case(UiAction::BinaryAxisZDown, 2, -1.0)]
    fn axis_buttons_tilt_one_component_of_the_selected_hole(
        #[case] action: UiAction,
        #[case] component: usize,
        #[case] sign: f32,
    ) {
        let mut app = ui_app();
        {
            let mut binary = app.world_mut().resource_mut::<BinaryBlackHoles>();
            binary.enabled = true;
            binary.selected = 1;
            binary.spins[1] = BinarySpin::new(0.5, Vec3::ONE);
        }
        app.world_mut().resource_mut::<SimObjects>().0.clear();
        click(&mut app, action);
        let axis = binary(&app).spins[1].axis.to_array();
        let other = (component + 1) % 3;
        assert_eq!((axis[component] - axis[other]).signum(), sign, "{axis:?}");
        assert_eq!(axis[other], axis[(component + 2) % 3]);
        assert_eq!(binary(&app).spins[0].axis, Vec3::Y, "hole A untouched");
        assert_eq!(scene_len(&app), 2, "scene rebuilt");
        assert!(cam(&app).is_moving);
    }

    #[rstest]
    #[case::wraps_back(UiAction::SkyboxPrev, 0, 3)]
    #[case::wraps_forward(UiAction::SkyboxNext, 3, 0)]
    #[case::next(UiAction::SkyboxNext, 1, 2)]
    fn skybox_buttons_cycle_and_bind_the_image(
        #[case] action: UiAction,
        #[case] start: usize,
        #[case] expected: usize,
    ) {
        let mut app = ui_app();
        app.world_mut().resource_mut::<SkyboxSet>().current = start;
        click(&mut app, action);
        let set = app.world().resource::<SkyboxSet>();
        assert_eq!(set.current, expected);
        assert_eq!(
            app.world().resource::<SkyboxImage>().0,
            set.handles[expected]
        );
        assert!(cam(&app).is_moving);
    }

    #[rstest]
    #[case::prev_wraps(UiAction::DiskModelPrev, DiskModel::ThinNt, DiskModel::WarpedThin)]
    #[case::next(
        UiAction::DiskModelNext,
        DiskModel::ThinNt,
        DiskModel::TruncatedHotFlow
    )]
    #[case::next_wraps(UiAction::DiskModelNext, DiskModel::WarpedThin, DiskModel::ThinNt)]
    fn model_buttons_load_presets_and_keep_spin(
        #[case] action: UiAction,
        #[case] start: DiskModel,
        #[case] expected: DiskModel,
    ) {
        let mut app = ui_app();
        *app.world_mut().resource_mut::<DiskConfig>() = DiskConfig::for_model(start, -0.2);
        click(&mut app, action);
        let preset = DiskConfig::for_model(expected.clone(), -0.2);
        assert_eq!(disk(&app).model, expected);
        assert_eq!(disk(&app).tilt_deg, preset.tilt_deg);
        assert_eq!(disk(&app).spin, -0.2);
        assert!(cam(&app).is_moving);
    }

    #[rstest]
    #[case::grid(UiAction::ToggleGrid, |app: &App| !app.world().resource::<GridVisible>().0, 2)]
    #[case::gravity(UiAction::ToggleGravity, |app: &App| app.world().resource::<GravityEnabled>().0, 2)]
    #[case::heatmap(UiAction::ToggleHeatmap, |app: &App| cam(app).debug_heatmap, 2)]
    #[case::debug_bodies(
        UiAction::ToggleDebugBodies,
        |app: &App| app.world().resource::<DebugBodiesEnabled>().0,
        3
    )]
    #[case::binary(UiAction::ToggleBinary, |app: &App| binary(app).enabled, 2)]
    fn toggle_buttons_flip_their_flags(
        #[case] action: UiAction,
        #[case] flipped: fn(&App) -> bool,
        // The default binary scene has 2 bodies; only some toggles rebuild it.
        #[case] scene_bodies: usize,
    ) {
        let mut app = ui_app();
        assert!(!flipped(&app));
        click(&mut app, action);
        assert!(flipped(&app));
        assert_eq!(scene_len(&app), scene_bodies);
        click(&mut app, action);
        assert!(!flipped(&app), "second press flips back");
    }

    fn display_text(app: &mut App, display: ValueDisplay) -> String {
        let entity = app.world_mut().spawn((Text::default(), display)).id();
        app.update();
        app.world().get::<Text>(entity).unwrap().0.clone()
    }

    #[rstest]
    #[case(ValueDisplay::Spin, "+0.82")]
    #[case(ValueDisplay::DiskRadius, "15 r_s")]
    #[case(ValueDisplay::MaxIter, "10000")]
    #[case(ValueDisplay::Fov, "60 deg")]
    #[case(ValueDisplay::RenderScale, "50%")]
    #[case(ValueDisplay::Skybox, "Checker Grid")]
    #[case(ValueDisplay::DiskModel, "Thin NT")]
    #[case(ValueDisplay::Polarization, "Intensity")]
    #[case(ValueDisplay::Frequency, "230")]
    #[case(ValueDisplay::Faraday, "1.00")]
    #[case(ValueDisplay::Conversion, "0.3")]
    #[case(ValueDisplay::BinaryHole, "A")]
    #[case(ValueDisplay::BinaryAxisX, "+0.00")]
    #[case(ValueDisplay::BinaryAxisY, "+1.00")]
    #[case(ValueDisplay::BinaryAxisZ, "+0.00")]
    fn value_displays_format_the_default_state(
        #[case] display: ValueDisplay,
        #[case] expected: &str,
    ) {
        assert_eq!(display_text(&mut ui_app(), display), expected);
    }

    #[rstest]
    #[case::unsigned_magnitude(ValueDisplay::Spin, "0.40")]
    #[case::selected_label(ValueDisplay::BinaryHole, "B")]
    #[case::axis_x(ValueDisplay::BinaryAxisX, "-0.60")]
    #[case::axis_z(ValueDisplay::BinaryAxisZ, "+0.80")]
    fn value_displays_follow_the_selected_binary_hole(
        #[case] display: ValueDisplay,
        #[case] expected: &str,
    ) {
        let mut app = ui_app();
        {
            let mut binary = app.world_mut().resource_mut::<BinaryBlackHoles>();
            binary.enabled = true;
            binary.selected = 1;
            binary.spins[1] = BinarySpin::new(0.4, Vec3::new(-3.0, 0.0, 4.0));
        }
        assert_eq!(display_text(&mut app, display), expected);
    }

    #[rstest]
    fn toggle_colours_show_state_and_hover(
        #[values(
            ToggleLabel::Grid,
            ToggleLabel::Gravity,
            ToggleLabel::Heatmap,
            ToggleLabel::Binary,
            ToggleLabel::DebugBodies
        )]
        label: ToggleLabel,
        #[values(false, true)] active: bool,
        #[values(false, true)] hovered: bool,
    ) {
        let mut app = ui_app();
        let world = app.world_mut();
        match label {
            ToggleLabel::Grid => world.resource_mut::<GridVisible>().0 = active,
            ToggleLabel::Gravity => world.resource_mut::<GravityEnabled>().0 = active,
            ToggleLabel::Heatmap => world.resource_mut::<OrbitalCamera>().debug_heatmap = active,
            ToggleLabel::Binary => world.resource_mut::<BinaryBlackHoles>().enabled = active,
            ToggleLabel::DebugBodies => world.resource_mut::<DebugBodiesEnabled>().0 = active,
        }
        let toggle = world
            .spawn((Hovered(hovered), BackgroundColor::default(), label))
            .id();
        app.update();
        let expected = match (active, hovered) {
            (true, false) => TOGGLE_ON,
            (true, true) => TOGGLE_ON_HOVER,
            (false, false) => TOGGLE_OFF,
            (false, true) => TOGGLE_OFF_HOVER,
        };
        assert_eq!(
            app.world().get::<BackgroundColor>(toggle).unwrap().0,
            expected
        );
    }

    #[rstest]
    #[case::hovered(true, BTN_HOVER)]
    #[case::normal(false, BTN_NORMAL)]
    fn arrow_buttons_highlight_on_hover(#[case] hovered: bool, #[case] expected: Color) {
        let mut app = App::new();
        app.add_systems(Update, step_button_colors);
        let arrow = app
            .world_mut()
            .spawn((
                Hovered(!hovered),
                BackgroundColor::default(),
                UiAction::FovUp,
            ))
            .id();
        app.update();
        // Re-inserting the immutable `Hovered` is how hover changes arrive.
        app.world_mut().entity_mut(arrow).insert(Hovered(hovered));
        app.update();
        assert_eq!(
            app.world().get::<BackgroundColor>(arrow).unwrap().0,
            expected
        );
    }
}
