use bevy::{
    asset::RenderAssetUsages,
    prelude::*,
    window::PrimaryWindow,
    render::{
        extract_resource::{ExtractResource, ExtractResourcePlugin},
        render_graph::{RenderGraph, RenderLabel},
        Render, RenderApp, RenderStartup, RenderSystems,
    },
};

mod pipeline;
use pipeline::{init_geodesic_pipeline, prepare_bind_group, GeodesicNode};

use crate::{camera::OrbitalCamera, simulation::SimObjects};

pub struct GeodesicComputePlugin;

// ── Resources extracted from main world → render world ──────────────────────

/// Handle to the texture the compute shader writes into.
#[derive(Resource, Clone, ExtractResource)]
pub struct GeodesicImage(pub Handle<Image>);

/// Camera data packed for the uniform buffer (matches the WGSL struct layout).
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
    pub _pad4: u32,
}

/// Object data packed for the uniform buffer.
#[derive(Resource, Clone, ExtractResource)]
pub struct ObjectsUniform {
    pub num_objects: i32,
    pub _pad: [f32; 3],
    /// xyz = position, w = radius
    pub pos_radius: [[f32; 4]; 16],
    pub color: [[f32; 4]; 16],
    /// std140 pads f32 array elements to 16 bytes; only [0] used
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

// ── Render graph node label ──────────────────────────────────────────────────

#[derive(Debug, Hash, PartialEq, Eq, Clone, RenderLabel)]
pub struct GeodesicLabel;

// ── Plugin ───────────────────────────────────────────────────────────────────

impl Plugin for GeodesicComputePlugin {
    fn build(&self, app: &mut App) {
        app.add_plugins((
            ExtractResourcePlugin::<GeodesicImage>::default(),
            ExtractResourcePlugin::<CameraUniform>::default(),
            ExtractResourcePlugin::<ObjectsUniform>::default(),
        ));

        app.init_resource::<CameraUniform>()
            .init_resource::<ObjectsUniform>();

        app.add_systems(Startup, setup_compute_texture);
        app.add_systems(Update, (sync_camera_uniform, sync_objects_uniform));

        let render_app = app.sub_app_mut(RenderApp);
        render_app
            .add_systems(RenderStartup, init_geodesic_pipeline)
            .add_systems(
                Render,
                prepare_bind_group.in_set(RenderSystems::PrepareBindGroups),
            );

        let mut graph = render_app.world_mut().resource_mut::<RenderGraph>();
        graph.add_node(GeodesicLabel, GeodesicNode::default());
        graph.add_node_edge(GeodesicLabel, bevy::render::graph::CameraDriverLabel);
    }
}

// ── Startup: create output texture + display sprite ─────────────────────────

fn setup_compute_texture(
    mut commands: Commands,
    mut images: ResMut<Assets<Image>>,
    windows: Query<&Window, With<PrimaryWindow>>,
) {
    use bevy::render::render_resource::{TextureFormat, TextureUsages};

    let (win_w, win_h) = windows.single().ok()
        .map(|win| (win.physical_width(), win.physical_height()))
        .unwrap_or((800, 600));
    // Render at half resolution, upscale 2× via sprite — halves GPU load
    let (w, h) = ((win_w / 2).max(1), (win_h / 2).max(1));

    let mut image = Image::new_target_texture(w, h, TextureFormat::Rgba8Unorm, None);
    image.asset_usage = RenderAssetUsages::RENDER_WORLD;
    image.texture_descriptor.usage =
        TextureUsages::COPY_DST | TextureUsages::STORAGE_BINDING | TextureUsages::TEXTURE_BINDING;

    let handle = images.add(image);

    commands.spawn((
        Sprite {
            image: handle.clone(),
            custom_size: Some(Vec2::new(win_w as f32, win_h as f32)),
            ..default()
        },
        Transform::default(),
    ));

    commands.insert_resource(GeodesicImage(handle));
}

// ── Per-frame uniform syncs ──────────────────────────────────────────────────

fn sync_camera_uniform(
    cam: Res<OrbitalCamera>,
    mut uniform: ResMut<CameraUniform>,
    windows: Query<&Window, With<PrimaryWindow>>,
) {
    let aspect = windows.single().ok()
        .map(|w| if w.height() > 0.0 { w.width() / w.height() } else { 800.0 / 600.0 })
        .unwrap_or(800.0 / 600.0);

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
        _pad4: 0,
    };
}

fn sync_objects_uniform(objects: Res<SimObjects>, mut uniform: ResMut<ObjectsUniform>) {
    uniform.num_objects = objects.0.len().min(16) as i32;
    for (i, obj) in objects.0.iter().take(16).enumerate() {
        uniform.pos_radius[i] = [obj.position.x, obj.position.y, obj.position.z, obj.radius];
        uniform.color[i] = obj.color.to_array();
        uniform.mass[i] = [obj.mass, 0.0, 0.0, 0.0];
    }
}
