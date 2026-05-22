use bevy::{
    asset::RenderAssetUsages,
    prelude::*,
    render::{
        Render, RenderApp, RenderStartup, RenderSystems,
        extract_resource::{ExtractResource, ExtractResourcePlugin},
        render_graph::{RenderGraph, RenderLabel},
        render_resource::{Extent3d, TextureDimension, TextureFormat, TextureUsages},
    },
    window::PrimaryWindow,
};

mod pipeline;
use pipeline::{GeodesicNode, init_geodesic_pipeline, prepare_bind_group};

mod accumulate;
use accumulate::{AccumulateNode, init_accumulate_pipeline, prepare_accumulate_bind_group};

use crate::{
    camera::OrbitalCamera,
    simulation::{DiskConfig, KERR_SPIN, SimObjects},
};

pub struct GeodesicComputePlugin;

// ── Resources extracted from main world → render world ──────────────────────

/// Raw frame written by geodesic.wgsl each tick.
#[derive(Resource, Clone, ExtractResource)]
pub struct GeodesicImage(pub Handle<Image>);

/// Ping-pong accumulation buffer A (rgba32float).
#[derive(Resource, Clone, ExtractResource)]
pub struct AccumA(pub Handle<Image>);

/// Ping-pong accumulation buffer B (rgba32float).
#[derive(Resource, Clone, ExtractResource)]
pub struct AccumB(pub Handle<Image>);

/// Final blended output shown by the sprite.
#[derive(Resource, Clone, ExtractResource)]
pub struct DisplayImage(pub Handle<Image>);

/// HDR equirectangular skybox currently bound to the geodesic shader.
#[derive(Resource, Clone, ExtractResource)]
pub struct SkyboxImage(pub Handle<Image>);

/// All loaded skyboxes; main-world-only, drives the cycle-on-B-key UI.
#[derive(Resource)]
pub struct SkyboxSet {
    pub handles: Vec<Handle<Image>>,
    pub current: usize,
}

/// frame_count sent to the accumulate shader for this render frame.
/// 0 = reset history; ≥1 = blend with α=0.1.
#[derive(Resource, Clone, Default, ExtractResource)]
pub struct RenderFrameCount(pub u32);

/// Determines which ping-pong buffer is "prev" for this frame.
/// true → frame_count even → use b_prev bind group (writes to AccumA)
/// false → frame_count odd  → use a_prev bind group (writes to AccumB)
#[derive(Resource, Clone, Default, ExtractResource)]
pub struct FrameParity(pub bool);

/// Camera data packed for the uniform buffer (matches Camera struct in geodesic.wgsl, 96 bytes).
#[derive(Resource, Clone, Default, ExtractResource)]
pub struct CameraUniform {
    pub pos: Vec3,
    pub _pad0: f32,
    pub right: Vec3,
    pub _pad1: f32,
    pub up: Vec3,
    pub _pad2: f32,
    pub forward: Vec3,
    pub _pad3: f32,
    pub tan_half_fov: f32,
    pub aspect: f32,
    pub moving: u32,
    pub jitter_x: f32,
    pub jitter_y: f32,
    /// 1 = output iteration-count heatmap; 0 = normal render.
    pub debug_heatmap: u32,
    pub _pad6: f32,
    pub _pad7: f32,
}

/// Object data packed for the uniform buffer.
#[derive(Resource, Clone, ExtractResource)]
pub struct ObjectsUniform {
    pub num_objects: i32,
    pub _pad: [f32; 3],
    pub pos_radius: [[f32; 4]; 16],
    pub color: [[f32; 4]; 16],
    pub mass: [[f32; 4]; 16],
}

impl Default for ObjectsUniform {
    fn default() -> Self {
        Self {
            num_objects: 0,
            _pad: [0.0; 3],
            pos_radius: [[0.0; 4]; 16],
            color: [[0.0; 4]; 16],
            mass: [[0.0; 4]; 16],
        }
    }
}

/// Disk/BH parameters extracted from `DiskConfig` each frame for the render world.
#[derive(Resource, Clone, ExtractResource)]
pub struct DiskConfigUniform {
    pub spin: f32,
    pub r_outer_rs: f32,
    pub model: u32,
    pub h_thin: f32,
    pub h_hot: f32,
    pub r_trunc_rs: f32,
    pub tilt_deg: f32,
    pub r_bp_rs: f32,
    pub twist_deg: f32,
}

impl Default for DiskConfigUniform {
    fn default() -> Self {
        Self {
            spin: KERR_SPIN,
            r_outer_rs: 15.0,
            model: 0,
            h_thin: 0.03,
            h_hot: 0.5,
            r_trunc_rs: 10.0,
            tilt_deg: 0.0,
            r_bp_rs: 5.0,
            twist_deg: 0.0,
        }
    }
}

/// Running count of still frames (main-world only, not extracted).
/// Drives jitter and frame_count sent to the GPU.
#[derive(Resource, Default)]
struct StillFrameCounter(u32);

/// Fraction of the window resolution used for compute textures (0.25–1.0).
/// Press `[` / `]` to cycle through presets at runtime.
#[derive(Resource)]
struct RenderScale(f32);

impl Default for RenderScale {
    fn default() -> Self {
        Self(0.5)
    }
}

/// Marks the sprite that displays the final rendered image so it can be
/// found and updated when the render scale changes.
#[derive(Component)]
struct DisplaySprite;

/// Tracks the (physical window size, render scale) that the current compute
/// textures were created for. `sync_compute_textures` compares against this
/// and recreates textures only when something changes.
#[derive(Resource)]
struct ComputeTexState {
    win_w: u32,
    win_h: u32,
    scale: f32,
}

// ── Render graph labels ──────────────────────────────────────────────────────

#[derive(Debug, Hash, PartialEq, Eq, Clone, RenderLabel)]
pub struct GeodesicLabel;

#[derive(Debug, Hash, PartialEq, Eq, Clone, RenderLabel)]
pub struct AccumulateLabel;

// ── Plugin ───────────────────────────────────────────────────────────────────

impl Plugin for GeodesicComputePlugin {
    fn build(&self, app: &mut App) {
        app.add_plugins((
            ExtractResourcePlugin::<GeodesicImage>::default(),
            ExtractResourcePlugin::<AccumA>::default(),
            ExtractResourcePlugin::<AccumB>::default(),
            ExtractResourcePlugin::<DisplayImage>::default(),
            ExtractResourcePlugin::<CameraUniform>::default(),
            ExtractResourcePlugin::<ObjectsUniform>::default(),
            ExtractResourcePlugin::<RenderFrameCount>::default(),
            ExtractResourcePlugin::<FrameParity>::default(),
            ExtractResourcePlugin::<DiskConfigUniform>::default(),
            ExtractResourcePlugin::<SkyboxImage>::default(),
        ));

        app.init_resource::<CameraUniform>()
            .init_resource::<ObjectsUniform>()
            .init_resource::<RenderFrameCount>()
            .init_resource::<FrameParity>()
            .init_resource::<DiskConfigUniform>()
            .init_resource::<StillFrameCounter>()
            .init_resource::<RenderScale>();

        app.add_systems(Startup, (setup_compute_texture, load_skyboxes));
        app.add_systems(
            Update,
            (
                sync_camera_uniform,
                sync_objects_uniform,
                sync_disk_config_uniform,
                cycle_skybox,
                (cycle_render_scale, sync_compute_textures).chain(),
            ),
        );

        let render_app = app.sub_app_mut(RenderApp);
        render_app
            .add_systems(
                RenderStartup,
                (init_geodesic_pipeline, init_accumulate_pipeline),
            )
            .add_systems(
                Render,
                (prepare_bind_group, prepare_accumulate_bind_group)
                    .in_set(RenderSystems::PrepareBindGroups),
            );

        let mut graph = render_app.world_mut().resource_mut::<RenderGraph>();
        graph.add_node(GeodesicLabel, GeodesicNode::default());
        graph.add_node(AccumulateLabel, AccumulateNode::default());
        graph.add_node_edge(GeodesicLabel, AccumulateLabel);
        graph.add_node_edge(AccumulateLabel, bevy::render::graph::CameraDriverLabel);
    }
}

// ── Startup: create all textures + display sprite ────────────────────────────

fn make_rgba8_tex(w: u32, h: u32, images: &mut Assets<Image>) -> Handle<Image> {
    let mut img = Image::new_target_texture(w, h, TextureFormat::Rgba8Unorm, None);
    img.asset_usage = RenderAssetUsages::RENDER_WORLD;
    img.texture_descriptor.usage =
        TextureUsages::COPY_DST | TextureUsages::STORAGE_BINDING | TextureUsages::TEXTURE_BINDING;
    images.add(img)
}

fn make_rgba32f_tex(w: u32, h: u32, images: &mut Assets<Image>) -> Handle<Image> {
    let mut img = Image::new_fill(
        Extent3d {
            width: w,
            height: h,
            depth_or_array_layers: 1,
        },
        TextureDimension::D2,
        &[0u8; 16], // 4 × f32 = 16 bytes; represents [0,0,0,0]
        TextureFormat::Rgba32Float,
        RenderAssetUsages::RENDER_WORLD,
    );
    img.texture_descriptor.usage =
        TextureUsages::COPY_DST | TextureUsages::STORAGE_BINDING | TextureUsages::TEXTURE_BINDING;
    images.add(img)
}

fn setup_compute_texture(
    mut commands: Commands,
    mut images: ResMut<Assets<Image>>,
    windows: Query<&Window, With<PrimaryWindow>>,
    scale: Res<RenderScale>,
) {
    let (win_w, win_h) = windows
        .single()
        .ok()
        .map(|win| (win.physical_width(), win.physical_height()))
        .unwrap_or((800, 600));
    let w = ((win_w as f32 * scale.0) as u32).max(1);
    let h = ((win_h as f32 * scale.0) as u32).max(1);

    commands.insert_resource(GeodesicImage(make_rgba8_tex(w, h, &mut images)));
    commands.insert_resource(AccumA(make_rgba32f_tex(w, h, &mut images)));
    commands.insert_resource(AccumB(make_rgba32f_tex(w, h, &mut images)));

    let disp = make_rgba8_tex(w, h, &mut images);
    commands.spawn((
        Sprite {
            image: disp.clone(),
            custom_size: Some(Vec2::new(win_w as f32, win_h as f32)),
            ..default()
        },
        Transform::default(),
        DisplaySprite,
    ));
    commands.insert_resource(DisplayImage(disp));
    commands.insert_resource(ComputeTexState { win_w, win_h, scale: scale.0 });
}

// ── Per-frame uniform syncs ──────────────────────────────────────────────────

/// Halton low-discrepancy sequence, 1-indexed. Returns value in [0, 1).
fn halton(mut i: u32, base: u32) -> f32 {
    let mut f = 1.0_f32;
    let mut r = 0.0_f32;
    while i > 0 {
        f /= base as f32;
        r += f * (i % base) as f32;
        i /= base;
    }
    r
}

fn sync_camera_uniform(
    cam: Res<OrbitalCamera>,
    mut uniform: ResMut<CameraUniform>,
    mut counter: ResMut<StillFrameCounter>,
    mut render_fc: ResMut<RenderFrameCount>,
    mut parity: ResMut<FrameParity>,
    windows: Query<&Window, With<PrimaryWindow>>,
) {
    let aspect = windows
        .single()
        .ok()
        .map(|w| {
            if w.height() > 0.0 {
                w.width() / w.height()
            } else {
                800.0 / 600.0
            }
        })
        .unwrap_or(800.0 / 600.0);

    // fc = frame_count sent to the GPU for THIS render frame.
    // 0 means "reset accumulation", ≥1 means "blend".
    let fc = if cam.is_moving { 0u32 } else { counter.0 };
    render_fc.0 = fc;
    // even fc → parity=true → b_prev bind group (writes into AccumA)
    parity.0 = fc % 2 == 0;

    // Suppress jitter in heatmap mode: each frame is deterministic so averaging
    // slightly-shifted heatmaps would blur the per-pixel iteration counts.
    let (jx, jy) = if cam.is_moving || cam.debug_heatmap {
        (0.0f32, 0.0f32)
    } else {
        // Halton(1,2)=0.5 → jx=0 on first still frame, varies thereafter.
        (halton(fc + 1, 2) - 0.5, halton(fc + 1, 3) - 0.5)
    };

    // Advance counter for the next frame.
    if cam.is_moving {
        counter.0 = 0;
    } else {
        counter.0 = counter.0.saturating_add(1);
    }

    *uniform = CameraUniform {
        pos: cam.position(),
        _pad0: 0.0,
        right: cam.right(),
        _pad1: 0.0,
        up: cam.up(),
        _pad2: 0.0,
        forward: cam.forward(),
        _pad3: 0.0,
        tan_half_fov: cam.tan_half_fov(),
        aspect,
        moving: cam.is_moving as u32,
        jitter_x: jx,
        jitter_y: jy,
        debug_heatmap: cam.debug_heatmap as u32,
        _pad6: 0.0,
        _pad7: 0.0,
    };
}

fn sync_objects_uniform(objects: Res<SimObjects>, mut uniform: ResMut<ObjectsUniform>) {
    if !objects.is_changed() {
        return;
    }
    uniform.num_objects = objects.0.len().min(16) as i32;
    for (i, obj) in objects.0.iter().take(16).enumerate() {
        uniform.pos_radius[i] = [obj.position.x, obj.position.y, obj.position.z, obj.radius];
        uniform.color[i] = obj.color.to_array();
        uniform.mass[i] = [obj.mass, 0.0, 0.0, 0.0];
    }
}

fn sync_disk_config_uniform(disk: Res<DiskConfig>, mut uniform: ResMut<DiskConfigUniform>) {
    if !disk.is_changed() {
        return;
    }
    uniform.spin = disk.spin;
    uniform.r_outer_rs = disk.r_outer_rs;
    uniform.model = disk.model.as_u32();
    uniform.h_thin = disk.h_thin;
    uniform.h_hot = disk.h_hot;
    uniform.r_trunc_rs = disk.r_trunc_rs;
    uniform.tilt_deg = disk.tilt_deg;
    uniform.r_bp_rs = disk.r_bp_rs;
    uniform.twist_deg = disk.twist_deg;
}

const SCALE_PRESETS: &[f32] = &[0.25, 0.5, 0.75, 1.0];

/// Press `-` / `=` to step render scale down / up through 25 % → 50 % → 75 % → 100 %.
fn cycle_render_scale(keys: Res<ButtonInput<KeyCode>>, mut scale: ResMut<RenderScale>) {
    let idx = SCALE_PRESETS
        .iter()
        .position(|&s| (s - scale.0).abs() < 0.01)
        .unwrap_or(1);

    let new_idx = if keys.just_pressed(KeyCode::Minus) {
        idx.saturating_sub(1)
    } else if keys.just_pressed(KeyCode::Equal) {
        (idx + 1).min(SCALE_PRESETS.len() - 1)
    } else {
        return;
    };

    if new_idx != idx {
        scale.0 = SCALE_PRESETS[new_idx];
        info!("Render scale: {:.0}%", scale.0 * 100.0);
    }
}

/// Recreates compute/accum/display textures whenever the physical window size
/// or render scale changes. Also handles initial sizing at startup.
fn sync_compute_textures(
    mut state: ResMut<ComputeTexState>,
    scale: Res<RenderScale>,
    mut images: ResMut<Assets<Image>>,
    mut geo: ResMut<GeodesicImage>,
    mut accum_a: ResMut<AccumA>,
    mut accum_b: ResMut<AccumB>,
    mut display: ResMut<DisplayImage>,
    mut sprites: Query<&mut Sprite, With<DisplaySprite>>,
    windows: Query<&Window, With<PrimaryWindow>>,
    mut cam: ResMut<OrbitalCamera>,
) {
    let (win_w, win_h) = windows
        .single()
        .ok()
        .map(|w| (w.physical_width(), w.physical_height()))
        .unwrap_or((800, 600));

    if win_w == 0 || win_h == 0 {
        return;
    }

    if win_w == state.win_w && win_h == state.win_h && scale.0 == state.scale {
        return;
    }

    state.win_w = win_w;
    state.win_h = win_h;
    state.scale = scale.0;

    let w = ((win_w as f32 * scale.0) as u32).max(1);
    let h = ((win_h as f32 * scale.0) as u32).max(1);

    geo.0 = make_rgba8_tex(w, h, &mut images);
    accum_a.0 = make_rgba32f_tex(w, h, &mut images);
    accum_b.0 = make_rgba32f_tex(w, h, &mut images);
    let disp = make_rgba8_tex(w, h, &mut images);
    display.0 = disp.clone();

    if let Ok(mut sprite) = sprites.single_mut() {
        sprite.image = disp;
        sprite.custom_size = Some(Vec2::new(win_w as f32, win_h as f32));
    }

    cam.is_moving = true;
    info!(
        "Compute textures: {}×{} (window {}×{}, scale {:.0}%)",
        w,
        h,
        win_w,
        win_h,
        scale.0 * 100.0
    );
}

const SKYBOXES: &[&str] = &[
    "hdr/HDR_galactic_plane_1.hdr",
    "hdr/HDR_blue_nebulae_3.hdr",
    "hdr/HDR_white_local_star_and_nebulae.hdr",
];

fn load_skyboxes(mut commands: Commands, asset_server: Res<AssetServer>) {
    let handles: Vec<Handle<Image>> = SKYBOXES.iter().map(|p| asset_server.load(*p)).collect();
    commands.insert_resource(SkyboxImage(handles[0].clone()));
    commands.insert_resource(SkyboxSet {
        handles,
        current: 0,
    });
}

/// Press B to cycle through the loaded HDR skyboxes.
fn cycle_skybox(
    keys: Res<ButtonInput<KeyCode>>,
    mut set: ResMut<SkyboxSet>,
    mut active: ResMut<SkyboxImage>,
    mut cam: ResMut<OrbitalCamera>,
) {
    if keys.just_pressed(KeyCode::KeyB) {
        set.current = (set.current + 1) % set.handles.len();
        active.0 = set.handles[set.current].clone();
        cam.is_moving = true; // reset TAA history
        info!("Skybox: {} ({})", set.current, SKYBOXES[set.current]);
    }
}
