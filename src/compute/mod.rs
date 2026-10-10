use bevy::{
    asset::RenderAssetUsages,
    core_pipeline::schedule::camera_driver,
    ecs::system::SystemParam,
    prelude::*,
    render::{
        Render, RenderApp, RenderStartup, RenderSystems,
        extract_resource::{ExtractResource, ExtractResourcePlugin},
        render_resource::{Extent3d, TextureDimension, TextureFormat, TextureUsages},
        renderer::RenderGraph,
    },
    window::PrimaryWindow,
};

mod pipeline;
use pipeline::{dispatch_geodesic, init_geodesic_pipeline, prepare_bind_group};

mod accumulate;
use accumulate::{dispatch_accumulate, init_accumulate_pipeline, prepare_accumulate_bind_group};

use crate::{
    camera::OrbitalCamera,
    controller::active_gamepad,
    simulation::{BinaryBlackHoles, DiskConfig, KERR_SPIN, SimObjects},
};

pub struct GeodesicComputePlugin;

// ── Resources extracted from main world → render world ──────────────────────

/// Raw frame written by geodesic.wgsl each tick.
#[derive(Resource, Clone, ExtractResource)]
#[extract_app(RenderApp)]
pub struct GeodesicImage(pub Handle<Image>);

/// Ping-pong accumulation buffer A (rgba32float).
#[derive(Resource, Clone, ExtractResource)]
#[extract_app(RenderApp)]
pub struct AccumA(pub Handle<Image>);

/// Ping-pong accumulation buffer B (rgba32float).
#[derive(Resource, Clone, ExtractResource)]
#[extract_app(RenderApp)]
pub struct AccumB(pub Handle<Image>);

/// Final blended output shown by the sprite.
#[derive(Resource, Clone, ExtractResource)]
#[extract_app(RenderApp)]
pub struct DisplayImage(pub Handle<Image>);

/// HDR equirectangular skybox currently bound to the geodesic shader.
#[derive(Resource, Clone, ExtractResource)]
#[extract_app(RenderApp)]
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
#[extract_app(RenderApp)]
pub struct RenderFrameCount(pub u32);

/// Determines which ping-pong buffer is "prev" for this frame.
/// true → frame_count even → use b_prev bind group (writes to AccumA)
/// false → frame_count odd  → use a_prev bind group (writes to AccumB)
#[derive(Resource, Clone, Default, ExtractResource)]
#[extract_app(RenderApp)]
pub struct FrameParity(pub bool);

/// Camera data packed for the uniform buffer (matches Camera struct in geodesic.wgsl, 112 bytes).
#[derive(Resource, Clone, Default, ExtractResource)]
#[extract_app(RenderApp)]
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
    /// Maximum geodesic steps per pixel.
    pub max_iter: u32,
    pub polarization_view: u32,
    pub frequency_ghz: f32,
    pub faraday_depth: f32,
    pub conversion_depth: f32,
    pub _pad7: f32,
}

/// Object data packed for the uniform buffer.
#[derive(Resource, Clone, ExtractResource)]
#[extract_app(RenderApp)]
pub struct ObjectsUniform {
    pub num_objects: i32,
    pub _pad: [f32; 3],
    pub pos_radius: [[f32; 4]; 16],
    pub color: [[f32; 4]; 16],
    pub mass: [[f32; 4]; 16],
    pub spin: [[f32; 4]; 16],
}

impl Default for ObjectsUniform {
    fn default() -> Self {
        Self {
            num_objects: 0,
            _pad: [0.0; 3],
            pos_radius: [[0.0; 4]; 16],
            color: [[0.0; 4]; 16],
            mass: [[0.0; 4]; 16],
            spin: [[0.0; 4]; 16],
        }
    }
}

/// Disk/BH parameters extracted from `DiskConfig` each frame for the render world.
#[derive(Resource, Clone, ExtractResource)]
#[extract_app(RenderApp)]
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
    pub binary_enabled: bool,
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
            binary_enabled: true,
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
pub(crate) struct RenderScale(pub(crate) f32);

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
                cycle_skybox,
                (cycle_render_scale, sync_compute_textures).chain(),
            ),
        );
        // Uniforms read the frame's final state, including `is_moving` set during Update.
        app.add_systems(
            PostUpdate,
            (
                sync_camera_uniform,
                sync_objects_uniform,
                sync_disk_config_uniform,
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

        render_app.add_systems(
            RenderGraph,
            (dispatch_geodesic, dispatch_accumulate)
                .chain()
                .before(camera_driver),
        );
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

#[cfg_attr(test, mutants::skip)] // needs a window + render assets
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
    commands.insert_resource(ComputeTexState {
        win_w,
        win_h,
        scale: scale.0,
    });
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
    objects: Res<SimObjects>,
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
    let scene_moving = cam.is_moving
        || objects.is_changed()
        || uniform.polarization_view != cam.polarization_view
        || uniform.frequency_ghz != cam.frequency_ghz
        || uniform.faraday_depth != cam.faraday_depth
        || uniform.conversion_depth != cam.conversion_depth;
    let fc = if scene_moving { 0u32 } else { counter.0 };
    render_fc.0 = fc;
    // even fc → parity=true → b_prev bind group (writes into AccumA)
    parity.0 = fc % 2 == 0;

    // Suppress jitter in heatmap mode: each frame is deterministic so averaging
    // slightly-shifted heatmaps would blur the per-pixel iteration counts.
    let (jx, jy) = if scene_moving || cam.debug_heatmap {
        (0.0f32, 0.0f32)
    } else {
        // Halton(1,2)=0.5 → jx=0 on first still frame, varies thereafter.
        (halton(fc + 1, 2) - 0.5, halton(fc + 1, 3) - 0.5)
    };

    // Advance counter for the next frame.
    if scene_moving {
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
        moving: scene_moving as u32,
        jitter_x: jx,
        jitter_y: jy,
        debug_heatmap: cam.debug_heatmap as u32,
        max_iter: cam.max_iter,
        polarization_view: cam.polarization_view,
        frequency_ghz: cam.frequency_ghz,
        faraday_depth: cam.faraday_depth,
        conversion_depth: cam.conversion_depth,
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
        uniform.spin[i] = [obj.spin.x, obj.spin.y, obj.spin.z, 0.0];
    }
}

fn sync_disk_config_uniform(
    disk: Res<DiskConfig>,
    binary: Res<BinaryBlackHoles>,
    mut uniform: ResMut<DiskConfigUniform>,
) {
    if !disk.is_changed() && uniform.binary_enabled == binary.enabled {
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
    uniform.binary_enabled = binary.enabled;
}

pub(crate) const SCALE_PRESETS: &[f32] = &[0.25, 0.5, 0.75, 1.0];

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

#[derive(SystemParam)]
struct ComputeTexParams<'w> {
    images: ResMut<'w, Assets<Image>>,
    geo: ResMut<'w, GeodesicImage>,
    accum_a: ResMut<'w, AccumA>,
    accum_b: ResMut<'w, AccumB>,
    display: ResMut<'w, DisplayImage>,
}

/// Recreates compute/accum/display textures whenever the physical window size
/// or render scale changes. Also handles initial sizing at startup.
fn sync_compute_textures(
    mut state: ResMut<ComputeTexState>,
    scale: Res<RenderScale>,
    mut tex: ComputeTexParams,
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

    tex.geo.0 = make_rgba8_tex(w, h, &mut tex.images);
    tex.accum_a.0 = make_rgba32f_tex(w, h, &mut tex.images);
    tex.accum_b.0 = make_rgba32f_tex(w, h, &mut tex.images);
    let disp = make_rgba8_tex(w, h, &mut tex.images);
    tex.display.0 = disp.clone();

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

pub(crate) const HDR_SKYBOXES: &[&str] = &[
    "hdr/HDR_galactic_plane_1.hdr",
    "hdr/HDR_blue_nebulae_3.hdr",
    "hdr/HDR_white_local_star_and_nebulae.hdr",
];

pub(crate) const SKYBOX_NAMES: &[&str] = &[
    "Checker Grid",
    "Galactic Plane",
    "Blue Nebula",
    "Star Field",
];

fn make_checker_skybox(images: &mut Assets<Image>) -> Handle<Image> {
    const WIDTH: u32 = 1024;
    const HEIGHT: u32 = 512;
    const CHECK_SIZE: u32 = 32;

    let mut data = Vec::with_capacity((WIDTH * HEIGHT * 16) as usize);
    for y in 0..HEIGHT {
        for x in 0..WIDTH {
            let checker = ((x / CHECK_SIZE) + (y / CHECK_SIZE)).is_multiple_of(2);
            let color = if checker {
                [8.0_f32, 8.0, 8.0, 1.0]
            } else {
                [0.02_f32, 0.02, 0.02, 1.0]
            };
            for channel in color {
                data.extend_from_slice(&channel.to_ne_bytes());
            }
        }
    }

    let mut img = Image::new(
        Extent3d {
            width: WIDTH,
            height: HEIGHT,
            depth_or_array_layers: 1,
        },
        TextureDimension::D2,
        data,
        TextureFormat::Rgba32Float,
        RenderAssetUsages::RENDER_WORLD,
    );
    img.texture_descriptor.usage = TextureUsages::COPY_DST | TextureUsages::TEXTURE_BINDING;
    images.add(img)
}

fn load_skyboxes(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
    mut images: ResMut<Assets<Image>>,
) {
    let mut handles = vec![make_checker_skybox(&mut images)];
    handles.extend(HDR_SKYBOXES.iter().map(|p| asset_server.load(*p)));
    commands.insert_resource(SkyboxImage(handles[0].clone()));
    commands.insert_resource(SkyboxSet {
        handles,
        current: 0,
    });
}

/// Press B to cycle through the loaded HDR skyboxes.
fn cycle_skybox(
    keys: Res<ButtonInput<KeyCode>>,
    gamepads: Query<&Gamepad>,
    mut set: ResMut<SkyboxSet>,
    mut active: ResMut<SkyboxImage>,
    mut cam: ResMut<OrbitalCamera>,
) {
    let gamepad_pressed_a =
        active_gamepad(&gamepads).is_some_and(|gamepad| gamepad.just_pressed(GamepadButton::South));
    if keys.just_pressed(KeyCode::KeyB) || gamepad_pressed_a {
        set.current = (set.current + 1) % set.handles.len();
        active.0 = set.handles[set.current].clone();
        cam.is_moving = true; // reset TAA history
        info!("Skybox: {} ({})", set.current, SKYBOX_NAMES[set.current]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bevy::{
        render::{
            RenderPlugin,
            gpu_readback::{Readback, ReadbackComplete},
        },
        window::ExitCondition,
        winit::WinitPlugin,
    };
    use proptest::prelude::*;
    use rstest::rstest;
    use std::time::{Duration, Instant};

    #[derive(Resource, Default)]
    struct Pixels(Vec<u8>);

    // ── Halton jitter sequence ───────────────────────────────────────────────

    /// 1, 2, 3, 6 in base 2 → .1, .01, .11, .011; in base 3 → .1, .2, .01, .02
    #[rstest]
    #[case(0, 2, 0.0)]
    #[case(1, 2, 0.5)]
    #[case(2, 2, 0.25)]
    #[case(3, 2, 0.75)]
    #[case(6, 2, 0.375)]
    #[case(1, 3, 1.0 / 3.0)]
    #[case(2, 3, 2.0 / 3.0)]
    #[case(3, 3, 1.0 / 9.0)]
    #[case(6, 3, 2.0 / 9.0)]
    fn halton_matches_radical_inverse(#[case] i: u32, #[case] base: u32, #[case] expected: f32) {
        assert!(
            (halton(i, base) - expected).abs() < 1e-6,
            "{}",
            halton(i, base)
        );
    }

    proptest! {
        #[test]
        fn halton_is_a_self_similar_unit_interval_sequence(i in 1_u32..10_000, base in 2_u32..8) {
            let h = halton(i, base);
            prop_assert!((0.0..1.0).contains(&h), "{h}");
            // Appending a 0 digit (i·b) shifts the radical inverse one place right.
            prop_assert!((halton(i * base, base) - h / base as f32).abs() < 1e-6);
        }
    }

    // ── Camera uniform and accumulation ──────────────────────────────────────

    fn camera_sync_app() -> App {
        let mut app = App::new();
        app.init_resource::<OrbitalCamera>()
            .init_resource::<SimObjects>()
            .init_resource::<CameraUniform>()
            .init_resource::<StillFrameCounter>()
            .init_resource::<RenderFrameCount>()
            .init_resource::<FrameParity>()
            .add_systems(Update, sync_camera_uniform);
        app
    }

    /// (frame_count, parity, jitter_x, jitter_y, moving) after one update.
    fn sync_frame(app: &mut App) -> (u32, bool, f32, f32, u32) {
        app.update();
        let world = app.world();
        let uniform = world.resource::<CameraUniform>();
        (
            world.resource::<RenderFrameCount>().0,
            world.resource::<FrameParity>().0,
            uniform.jitter_x,
            uniform.jitter_y,
            uniform.moving,
        )
    }

    #[test]
    fn still_frames_count_up_and_movement_resets_accumulation() {
        let mut app = camera_sync_app();
        // First frame: SimObjects was just added, so the scene counts as moving.
        assert_eq!(sync_frame(&mut app), (0, true, 0.0, 0.0, 1));
        let (fc, parity, jx, jy, moving) = sync_frame(&mut app);
        assert_eq!((fc, parity, jx, moving), (0, true, 0.0, 0));
        assert!((jy + 1.0 / 6.0).abs() < 1e-6, "jitter_y = {jy}");
        let (fc, parity, jx, jy, _) = sync_frame(&mut app);
        assert_eq!((fc, parity, jx), (1, false, -0.25));
        assert!((jy - 1.0 / 6.0).abs() < 1e-6, "jitter_y = {jy}");

        app.world_mut().resource_mut::<OrbitalCamera>().is_moving = true;
        assert_eq!(sync_frame(&mut app), (0, true, 0.0, 0.0, 1));
        app.world_mut().resource_mut::<OrbitalCamera>().is_moving = false;
        assert_eq!(sync_frame(&mut app).0, 0, "counter restarts from zero");
        assert_eq!(sync_frame(&mut app).0, 1);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn still_frames_blend_with_sub_pixel_jitter(frames in 2_u32..120) {
            let mut app = camera_sync_app();
            let mut last = sync_frame(&mut app);
            for _ in 1..frames {
                last = sync_frame(&mut app);
                let (_, _, jx, jy, _) = last;
                prop_assert!((-0.5..0.5).contains(&jx) && (-0.5..0.5).contains(&jy), "({jx}, {jy})");
            }
            let (fc, parity, _, _, moving) = last;
            prop_assert_eq!(fc, frames - 2);
            prop_assert_eq!(parity, fc % 2 == 0);
            prop_assert_eq!(moving, 0);
        }

        #[test]
        fn camera_uniform_mirrors_the_orbital_camera(
            radius in 1.6_f64..160.0,
            azimuth in -10.0_f64..10.0,
            elevation in 0.1_f64..3.0,
            fov_degrees in 10.0_f64..170.0,
            max_iter in prop::sample::select(crate::camera::ITER_PRESETS),
            polarization_view in 0_u32..6,
            heatmap in any::<bool>(),
        ) {
            let mut app = camera_sync_app();
            let cam = OrbitalCamera {
                radius, azimuth, elevation, fov_degrees, max_iter, polarization_view,
                debug_heatmap: heatmap,
                frequency_ghz: 86.0,
                faraday_depth: -3.0,
                conversion_depth: 7.0,
                ..default()
            };
            app.insert_resource(cam);
            app.update();
            let cam = app.world().resource::<OrbitalCamera>();
            let u = app.world().resource::<CameraUniform>();
            prop_assert_eq!(u.pos, cam.position());
            prop_assert_eq!((u.right, u.up, u.forward), (cam.right(), cam.up(), cam.forward()));
            prop_assert_eq!(u.tan_half_fov, cam.tan_half_fov());
            prop_assert_eq!((u.max_iter, u.polarization_view), (max_iter, polarization_view));
            prop_assert_eq!(u.debug_heatmap, heatmap as u32);
            prop_assert_eq!((u.frequency_ghz, u.faraday_depth, u.conversion_depth), (86.0, -3.0, 7.0));
        }
    }

    #[rstest]
    #[case::polarization_view(|w: &mut World| w.resource_mut::<OrbitalCamera>().polarization_view = 2)]
    #[case::frequency(|w: &mut World| w.resource_mut::<OrbitalCamera>().frequency_ghz = 86.0)]
    #[case::faraday(|w: &mut World| w.resource_mut::<OrbitalCamera>().faraday_depth = -3.0)]
    #[case::conversion(|w: &mut World| w.resource_mut::<OrbitalCamera>().conversion_depth = 7.0)]
    #[case::objects(|w: &mut World| w.resource_mut::<SimObjects>().set_changed())]
    #[case::camera_motion(|w: &mut World| w.resource_mut::<OrbitalCamera>().is_moving = true)]
    fn scene_changes_reset_accumulation(#[case] edit: fn(&mut World)) {
        let mut app = camera_sync_app();
        for _ in 0..3 {
            sync_frame(&mut app);
        }
        assert_eq!(sync_frame(&mut app).0, 2, "accumulating before the change");
        edit(app.world_mut());
        assert_eq!(sync_frame(&mut app), (0, true, 0.0, 0.0, 1));
    }

    #[test]
    fn heatmap_suppresses_jitter_without_resetting() {
        let mut app = camera_sync_app();
        for _ in 0..3 {
            sync_frame(&mut app);
        }
        app.world_mut()
            .resource_mut::<OrbitalCamera>()
            .debug_heatmap = true;
        let (fc, _, jx, jy, moving) = sync_frame(&mut app);
        assert_eq!((fc, jx, jy, moving), (2, 0.0, 0.0, 0));
    }

    #[rstest]
    #[case::wide(1000.0, 400.0, 2.5)]
    #[case::square(600.0, 600.0, 1.0)]
    #[case::minimised_falls_back_to_4_3(1000.0, 0.0, 800.0 / 600.0)]
    fn aspect_ratio_comes_from_the_primary_window(
        #[case] width: f32,
        #[case] height: f32,
        #[case] expected: f32,
    ) {
        let mut app = camera_sync_app();
        let mut window = Window::default();
        window.resolution.set(width, height);
        app.world_mut().spawn((window, PrimaryWindow));
        app.update();
        assert_eq!(app.world().resource::<CameraUniform>().aspect, expected);
    }

    #[test]
    fn no_window_falls_back_to_4_3() {
        let mut app = camera_sync_app();
        app.update();
        assert_eq!(
            app.world().resource::<CameraUniform>().aspect,
            800.0 / 600.0
        );
    }

    // ── Object and disk uniforms ─────────────────────────────────────────────

    fn numbered_body(i: usize) -> crate::simulation::SimObject {
        crate::simulation::SimObject {
            position: Vec3::new(i as f32, 2.0 * i as f32, 3.0 * i as f32),
            radius: 0.5 + i as f32,
            color: Vec4::new(0.1, 0.2, 0.3, i as f32),
            mass: 7.0 * i as f32,
            velocity: Vec3::ZERO,
            spin: Vec3::new(0.125 * i as f32, 0.02, 0.03),
        }
    }

    fn objects_app(count: usize) -> App {
        let mut app = App::new();
        app.insert_resource(SimObjects((0..count).map(numbered_body).collect()))
            .init_resource::<ObjectsUniform>()
            .add_systems(Update, sync_objects_uniform);
        app.update();
        app
    }

    proptest! {
        #[test]
        fn objects_uniform_packs_up_to_sixteen_bodies(count in 0_usize..40) {
            let app = objects_app(count);
            let u = app.world().resource::<ObjectsUniform>();
            prop_assert_eq!(u.num_objects, count.min(16) as i32);
            for i in 0..count.min(16) {
                let body = numbered_body(i);
                prop_assert_eq!(u.pos_radius[i], body.position.extend(body.radius).to_array());
                prop_assert_eq!(u.color[i], body.color.to_array());
                prop_assert_eq!(u.mass[i], [body.mass, 0.0, 0.0, 0.0]);
                prop_assert_eq!(u.spin[i], body.spin.extend(0.0).to_array());
            }
        }

        #[test]
        fn disk_uniform_mirrors_disk_config(
            model in prop::sample::select(vec![
                crate::simulation::DiskModel::ThinNt,
                crate::simulation::DiskModel::TruncatedHotFlow,
                crate::simulation::DiskModel::SlimFunnel,
                crate::simulation::DiskModel::WarpedThin,
            ]),
            spin in -0.999_f32..=0.999,
            binary in any::<bool>(),
        ) {
            let disk = DiskConfig::for_model(model, spin);
            let mut app = App::new();
            app.insert_resource(disk.clone())
                .insert_resource(BinaryBlackHoles { enabled: binary, ..default() })
                .init_resource::<DiskConfigUniform>()
                .add_systems(Update, sync_disk_config_uniform);
            app.update();
            let u = app.world().resource::<DiskConfigUniform>();
            prop_assert_eq!((u.spin, u.r_outer_rs, u.model), (disk.spin, disk.r_outer_rs, disk.model.as_u32()));
            prop_assert_eq!((u.h_thin, u.h_hot, u.r_trunc_rs), (disk.h_thin, disk.h_hot, disk.r_trunc_rs));
            prop_assert_eq!((u.tilt_deg, u.r_bp_rs, u.twist_deg), (disk.tilt_deg, disk.r_bp_rs, disk.twist_deg));
            prop_assert_eq!(u.binary_enabled, binary);
        }
    }

    #[test]
    fn unchanged_objects_leave_the_uniform_alone() {
        let mut app = objects_app(3);
        app.world_mut().resource_mut::<ObjectsUniform>().num_objects = -1;
        app.update();
        assert_eq!(app.world().resource::<ObjectsUniform>().num_objects, -1);
    }

    #[test]
    fn binary_toggle_alone_resyncs_the_disk_uniform() {
        let mut app = App::new();
        app.init_resource::<DiskConfig>()
            .init_resource::<BinaryBlackHoles>()
            .init_resource::<DiskConfigUniform>()
            .add_systems(Update, sync_disk_config_uniform);
        app.update();
        app.update();
        app.world_mut().resource_mut::<BinaryBlackHoles>().enabled = false;
        app.update();
        assert!(!app.world().resource::<DiskConfigUniform>().binary_enabled);
    }

    // ── Render scale and skyboxes ────────────────────────────────────────────

    fn press_once<S: Resource>(app: &mut App, key: KeyCode) -> &S {
        app.world_mut()
            .resource_mut::<ButtonInput<KeyCode>>()
            .press(key);
        app.update();
        app.world_mut()
            .resource_mut::<ButtonInput<KeyCode>>()
            .reset_all();
        app.world().resource::<S>()
    }

    fn scale_app(start: f32) -> App {
        let mut app = App::new();
        app.init_resource::<ButtonInput<KeyCode>>()
            .insert_resource(RenderScale(start))
            .add_systems(Update, cycle_render_scale);
        app
    }

    #[rstest]
    #[case::down(0.5, KeyCode::Minus, 0.25)]
    #[case::stops_at_bottom(0.25, KeyCode::Minus, 0.25)]
    #[case::up(0.5, KeyCode::Equal, 0.75)]
    #[case::stops_at_top(1.0, KeyCode::Equal, 1.0)]
    #[case::off_preset_counts_as_half(0.6, KeyCode::Equal, 0.75)]
    #[case::unbound_key(0.5, KeyCode::KeyK, 0.5)]
    fn render_scale_keys_step_through_presets(
        #[case] start: f32,
        #[case] key: KeyCode,
        #[case] expected: f32,
    ) {
        let mut app = scale_app(start);
        assert_eq!(press_once::<RenderScale>(&mut app, key).0, expected);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn render_scale_keys_walk_the_preset_list(ups in prop::collection::vec(any::<bool>(), 0..10)) {
            let mut app = scale_app(0.5);
            let mut idx = 1;
            for up in ups {
                let key = if up { KeyCode::Equal } else { KeyCode::Minus };
                idx = if up { (idx + 1).min(SCALE_PRESETS.len() - 1) } else { idx.saturating_sub(1) };
                prop_assert_eq!(press_once::<RenderScale>(&mut app, key).0, SCALE_PRESETS[idx]);
            }
        }
    }

    #[rstest]
    #[case::advances(1, 2)]
    #[case::wraps(2, 0)]
    fn skybox_key_cycles_and_wraps(#[case] start: usize, #[case] expected: usize) {
        let mut images = Assets::<Image>::default();
        let handles: Vec<_> = (0..3).map(|_| images.add(Image::default())).collect();
        let mut app = App::new();
        app.init_resource::<ButtonInput<KeyCode>>()
            .init_resource::<OrbitalCamera>()
            .insert_resource(SkyboxImage(handles[start].clone()))
            .insert_resource(SkyboxSet {
                handles: handles.clone(),
                current: start,
            })
            .add_systems(Update, cycle_skybox);

        assert_eq!(
            press_once::<SkyboxSet>(&mut app, KeyCode::KeyB).current,
            expected
        );
        assert_eq!(app.world().resource::<SkyboxImage>().0, handles[expected]);
        assert!(app.world().resource::<OrbitalCamera>().is_moving);
    }

    /// The generated checker texture, built once for every test that inspects it.
    fn checker_image() -> &'static Image {
        static IMAGE: std::sync::LazyLock<Image> = std::sync::LazyLock::new(|| {
            let mut images = Assets::<Image>::default();
            let handle = make_checker_skybox(&mut images);
            images.get(&handle).unwrap().clone()
        });
        &IMAGE
    }

    #[test]
    fn checker_skybox_is_a_sampled_hdr_texture() {
        let image = checker_image();
        assert_eq!(image.size(), UVec2::new(1024, 512));
        assert_eq!(
            image.texture_descriptor.usage,
            TextureUsages::COPY_DST | TextureUsages::TEXTURE_BINDING
        );
    }

    proptest! {
        #[test]
        fn checker_skybox_alternates_32_pixel_squares(x in 0_usize..1024, y in 0_usize..512) {
            let data = checker_image().data.as_ref().unwrap();
            let at = (y * 1024 + x) * 16;
            let texel: Vec<f32> = data[at..at + 16]
                .as_chunks::<4>()
                .0
                .iter()
                .map(|c| f32::from_ne_bytes(*c))
                .collect();
            let bright = (x / 32 + y / 32) % 2 == 0;
            let level = if bright { 8.0 } else { 0.02 };
            prop_assert_eq!(texel, vec![level, level, level, 1.0]);
        }
    }

    #[test]
    #[ignore = "requires a GPU; run with cargo test headless_render -- --ignored --nocapture"]
    fn headless_render() {
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
                .disable::<WinitPlugin>()
                .disable::<bevy::render::pipelined_rendering::PipelinedRenderingPlugin>(),
        )
        .init_resource::<OrbitalCamera>()
        .init_resource::<SimObjects>()
        .init_resource::<DiskConfig>()
        .init_resource::<BinaryBlackHoles>()
        .init_resource::<Pixels>()
        .insert_resource(RenderScale(0.16)) // 128 x 96; 256-byte aligned rows for readback.
        .add_plugins(GeodesicComputePlugin)
        .add_systems(
            Startup,
            (|mut commands: Commands,
              output: Res<DisplayImage>,
              mut images: ResMut<Assets<Image>>| {
                images.get_mut(&output.0).unwrap().texture_descriptor.usage |=
                    TextureUsages::COPY_SRC;
                commands.spawn(Readback::texture(output.0.clone())).observe(
                    |event: On<ReadbackComplete>, mut pixels: ResMut<Pixels>| {
                        pixels.0 = event.data.clone();
                    },
                );
            })
            .after(setup_compute_texture),
        );
        while app.plugins_state() != bevy::app::PluginsState::Ready {
            bevy::tasks::tick_global_task_pools_on_main_thread();
        }
        app.finish();
        app.cleanup();
        {
            let world = app.world();
            pipeline::check_relativity(
                world.resource::<bevy::render::renderer::RenderDevice>(),
                world.resource::<bevy::render::renderer::RenderQueue>(),
            );
        }
        use crate::simulation::DiskModel;
        let mut previous = Vec::new();
        for (binary, model, view) in [
            (true, DiskModel::ThinNt, 0),
            (false, DiskModel::ThinNt, 0),
            (false, DiskModel::TruncatedHotFlow, 1),
            (false, DiskModel::TruncatedHotFlow, 2),
            (false, DiskModel::TruncatedHotFlow, 5),
            (true, DiskModel::TruncatedHotFlow, 1),
        ] {
            *app.world_mut().resource_mut::<DiskConfig>() = DiskConfig::for_model(model, KERR_SPIN);
            {
                let mut camera = app.world_mut().resource_mut::<OrbitalCamera>();
                camera.polarization_view = view;
                camera.is_moving = true; // deterministic rays, reset accumulation for every frame
                camera.frequency_ghz = 90.0;
                camera.conversion_depth = 3.0;
            }
            app.world_mut().resource_mut::<Pixels>().0.clear();
            app.world_mut().resource_mut::<BinaryBlackHoles>().enabled = binary;
            app.world_mut().resource_mut::<SimObjects>().0 = crate::simulation::scene_objects(
                KERR_SPIN,
                false,
                binary,
                0.0,
                crate::simulation::default_binary_spins(),
            );
            let deadline = Instant::now() + Duration::from_secs(30);
            let mut frames = 0;
            loop {
                app.update();
                app.world()
                    .resource::<bevy::render::renderer::RenderDevice>()
                    .poll(bevy::render::render_resource::PollType::Wait {
                        submission_index: None,
                        timeout: Some(Duration::from_secs(30)),
                    })
                    .unwrap();
                frames += 1;
                let pixels = &app.world().resource::<Pixels>().0;
                if frames >= 10
                    && pixels != &previous
                    && pixels.as_chunks::<4>().0.iter().any(|p| p[0] > 0)
                {
                    assert!(
                        pixels
                            .as_chunks::<4>()
                            .0
                            .iter()
                            .any(|p| p[..3] == [0, 0, 0])
                    );
                    if view == 1 {
                        assert!(
                            pixels
                                .as_chunks::<4>()
                                .0
                                .iter()
                                .all(|p| p[0] == p[1] && p[1] == p[2]),
                            "linear fraction must be grayscale"
                        );
                    }
                    previous = pixels.clone();
                    let image = Image::new(
                        Extent3d {
                            width: 128,
                            height: 96,
                            depth_or_array_layers: 1,
                        },
                        TextureDimension::D2,
                        pixels.clone(),
                        TextureFormat::Rgba8UnormSrgb,
                        RenderAssetUsages::MAIN_WORLD,
                    );
                    image
                        .try_into_dynamic()
                        .unwrap()
                        .save(format!("target/render-smoke-{binary}-{view}.png"))
                        .unwrap();
                    break;
                }
                assert!(
                    Instant::now() < deadline,
                    "no updated rendered pixels from GPU for binary={binary}, view={view}"
                );
            }
        }
    }
}
