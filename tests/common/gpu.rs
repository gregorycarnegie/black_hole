use bevy::{
    prelude::*,
    render::{
        RenderPlugin,
        render_resource::*,
        renderer::{RenderDevice, RenderQueue},
    },
    window::ExitCondition,
    winit::WinitPlugin,
};
use std::time::Duration;

pub fn run(
    source: &str,
    entry: &str,
    inputs: &[(&[u8], BufferUsages)],
    result_bytes: u64,
    workgroups: u32,
) -> Vec<u8> {
    let entries: Vec<_> = inputs
        .iter()
        .enumerate()
        .map(|(i, (data, usage))| (i as u32, *data, *usage))
        .collect();
    run_groups(source, entry, &[&entries], result_bytes, workgroups)
}

pub fn run_groups(
    source: &str,
    entry: &str,
    inputs: &[&[(u32, &[u8], BufferUsages)]],
    result_bytes: u64,
    workgroups: u32,
) -> Vec<u8> {
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
            .disable::<bevy::log::LogPlugin>()
            .disable::<bevy::gilrs::GilrsPlugin>()
            .disable::<WinitPlugin>()
            .disable::<bevy::render::pipelined_rendering::PipelinedRenderingPlugin>(),
    );
    while app.plugins_state() != bevy::app::PluginsState::Ready {
        bevy::tasks::tick_global_task_pools_on_main_thread();
    }
    app.finish();
    app.cleanup();
    let device = app.world().resource::<RenderDevice>();
    let queue = app.world().resource::<RenderQueue>();
    let shader = device.create_and_validate_shader_module(ShaderModuleDescriptor {
        label: Some(entry),
        source: ShaderSource::Wgsl(crate::common::compile_wesl(source).into()),
    });
    let pipeline = device.create_compute_pipeline(&RawComputePipelineDescriptor {
        label: Some(entry),
        layout: None,
        module: &shader,
        entry_point: Some(entry),
        compilation_options: default(),
        cache: None,
    });
    let upload = |data: &[u8], usage| {
        device.create_buffer_with_data(&BufferInitDescriptor {
            label: None,
            contents: data,
            usage,
        })
    };
    let results = device.create_buffer(&BufferDescriptor {
        label: None,
        size: result_bytes,
        usage: BufferUsages::STORAGE | BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let mut groups = Vec::new();
    for (index, entries) in inputs.iter().enumerate() {
        let buffers: Vec<_> = entries
            .iter()
            .map(|(_, data, usage)| upload(data, *usage))
            .collect();
        let mut bindings: Vec<_> = entries
            .iter()
            .zip(&buffers)
            .map(|((binding, _, _), buffer)| BindGroupEntry {
                binding: *binding,
                resource: buffer.as_entire_binding(),
            })
            .collect();
        if index + 1 == inputs.len() {
            let binding = entries
                .iter()
                .map(|(binding, _, _)| binding + 1)
                .max()
                .unwrap_or(0);
            bindings.push(BindGroupEntry {
                binding,
                resource: results.as_entire_binding(),
            });
        }
        groups.push(device.create_bind_group(
            None,
            &pipeline.get_bind_group_layout(index as u32).into(),
            &bindings,
        ));
    }
    let readback = device.create_buffer(&BufferDescriptor {
        label: None,
        size: result_bytes,
        usage: BufferUsages::MAP_READ | BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let mut encoder = device.create_command_encoder(&CommandEncoderDescriptor::default());
    {
        let mut pass = encoder.begin_compute_pass(&ComputePassDescriptor::default());
        pass.set_pipeline(&pipeline);
        for (index, group) in groups.iter().enumerate() {
            pass.set_bind_group(index as u32, group, &[]);
        }
        pass.dispatch_workgroups(workgroups, 1, 1);
    }
    encoder.copy_buffer_to_buffer(&results, 0, &readback, 0, result_bytes);
    queue.submit([encoder.finish()]);
    let (sender, receiver) = std::sync::mpsc::channel();
    readback
        .slice(..)
        .map_async(MapMode::Read, move |r| sender.send(r).unwrap());
    device
        .poll(PollType::Wait {
            submission_index: None,
            timeout: Some(Duration::from_secs(30)),
        })
        .unwrap();
    receiver
        .recv_timeout(Duration::from_secs(30))
        .unwrap()
        .unwrap();
    let data = readback.slice(..).get_mapped_range().unwrap();
    data.to_vec()
}
