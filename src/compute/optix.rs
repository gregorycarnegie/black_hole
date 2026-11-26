//! Experimental OptiX ray queries for the swarm (cargo feature `optix`).

#[allow(
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    clippy::all,
    dead_code
)]
mod sys {
    include!(concat!(env!("OUT_DIR"), "/optix.rs"));
}

use std::ffi::c_void;

use cudarc::driver::{CudaFunction, LaunchConfig, PushKernelArg};

use super::cuda::shared_cuda;

pub(crate) struct Optix {
    table: sys::OptixFunctionTable,
    context: sys::OptixDeviceContext,
    _library: libloading::Library,
}

fn check(result: sys::OptixResult, what: &str) -> Result<(), String> {
    if result == sys::OptixResult_OPTIX_SUCCESS {
        Ok(())
    } else {
        Err(format!("{what} failed with OptixResult {result}"))
    }
}

/// The driver ships nvoptix.dll in its driver-store folder rather than System32.
fn open_runtime() -> Result<libloading::Library, String> {
    if let Ok(library) = unsafe { libloading::Library::new("nvoptix.dll") } {
        return Ok(library);
    }
    let store = std::path::Path::new(r"C:\Windows\System32\DriverStore\FileRepository");
    let entries = std::fs::read_dir(store).map_err(|e| format!("{}: {e}", store.display()))?;
    for entry in entries.flatten() {
        let candidate = entry.path().join("nvoptix.dll");
        if candidate.is_file() {
            return unsafe { libloading::Library::new(&candidate) }
                .map_err(|e| format!("{}: {e}", candidate.display()));
        }
    }
    Err("nvoptix.dll not found; OptiX needs an NVIDIA driver R570 or newer".into())
}

impl Optix {
    pub(crate) fn new() -> Result<Self, String> {
        type Query = unsafe extern "C" fn(
            abi: i32,
            options: u32,
            keys: *mut c_void,
            values: *mut *const c_void,
            table: *mut c_void,
            size: usize,
        ) -> sys::OptixResult;
        let library = open_runtime()?;
        let mut table = sys::OptixFunctionTable::default();
        unsafe {
            let query: libloading::Symbol<Query> = library
                .get(b"optixQueryFunctionTable\0")
                .map_err(|e| format!("optixQueryFunctionTable: {e}"))?;
            check(
                query(
                    sys::OPTIX_ABI_VERSION as i32,
                    0,
                    std::ptr::null_mut(),
                    std::ptr::null_mut(),
                    (&raw mut table).cast(),
                    std::mem::size_of::<sys::OptixFunctionTable>(),
                ),
                "optixQueryFunctionTable",
            )?;
        }
        let cuda = shared_cuda();
        cuda.bind_to_thread();
        let cu_context = cuda.stream.context().cu_ctx() as sys::CUcontext;
        let options = sys::OptixDeviceContextOptions::default();
        let mut context = std::ptr::null_mut();
        let create = table
            .optixDeviceContextCreate
            .ok_or("missing optixDeviceContextCreate")?;
        check(
            unsafe { create(cu_context, &options, &mut context) },
            "optixDeviceContextCreate",
        )?;
        Ok(Self {
            table,
            context,
            _library: library,
        })
    }
}

impl Drop for Optix {
    fn drop(&mut self) {
        if let Some(destroy) = self.table.optixDeviceContextDestroy {
            unsafe { destroy(self.context) };
        }
    }
}

/// Raw device memory, freed on drop.
struct DeviceBuffer(sys::CUdeviceptr);

impl DeviceBuffer {
    fn new(bytes: usize) -> Self {
        Self(unsafe { cudarc::driver::result::malloc_sync(bytes.max(16)).unwrap() })
    }

    fn from<T>(data: &[T]) -> Self {
        let buffer = Self::new(std::mem::size_of_val(data));
        unsafe { cudarc::driver::result::memcpy_htod_sync(buffer.0, data).unwrap() };
        buffer
    }
}

impl Drop for DeviceBuffer {
    fn drop(&mut self) {
        unsafe { cudarc::driver::result::free_sync(self.0).unwrap() };
    }
}

/// Matches `SegmentQueries` in `tools/optix/programs.rs`.
#[repr(C)]
#[derive(Clone, Copy)]
struct SegmentQueries {
    segments: u64,
    bodies: u64,
    results: u64,
    handle: u64,
    count: u32,
    backoff: f32,
}

const PROGRAMS_PTX: &str = include_str!("../../tools/optix/black_hole_optix_programs.ptx");
const SBT_HEADER: usize = 32;
const SBT_RECORD: usize = 48;
/// Keyframes cover camera-relative times [TIME_BEGIN, TIME_END].
const TIME_BEGIN: f32 = -412.0;
const TIME_END: f32 = 6.0;
const KEYS: u16 = 53;
/// Steps the BVH accepts span at most this much time; OptiX rays use the mid time.
const STEP_SPAN: f32 = 12.0;

/// One compiled pipeline answering swarm segment queries with RT cores.
pub(crate) struct SegmentPipeline {
    optix: Optix,
    pipeline: sys::OptixPipeline,
    groups: [sys::OptixProgramGroup; 3],
}

impl SegmentPipeline {
    fn compile_options() -> (
        sys::OptixModuleCompileOptions,
        sys::OptixPipelineCompileOptions,
    ) {
        let module = sys::OptixModuleCompileOptions::default();
        let pipeline = sys::OptixPipelineCompileOptions {
            usesMotionBlur: 1,
            numPayloadValues: 3,
            numAttributeValues: 1,
            usesPrimitiveTypeFlags: sys::OptixPrimitiveTypeFlags_OPTIX_PRIMITIVE_TYPE_FLAGS_SPHERE
                as u32,
            ..Default::default()
        };
        (module, pipeline)
    }

    pub(crate) fn new() -> Result<Self, String> {
        let optix = Optix::new()?;
        let t = &optix.table;
        let (module_options, pipeline_options) = Self::compile_options();
        let mut log = vec![0u8; 8192];
        let log_text = |log: &[u8]| {
            String::from_utf8_lossy(log)
                .trim_end_matches('\0')
                .to_string()
        };

        let mut module = std::ptr::null_mut();
        let mut size = log.len();
        let result = unsafe {
            t.optixModuleCreate.unwrap()(
                optix.context,
                &module_options,
                &pipeline_options,
                PROGRAMS_PTX.as_ptr().cast(),
                PROGRAMS_PTX.len(),
                log.as_mut_ptr().cast(),
                &mut size,
                &mut module,
            )
        };
        check(
            result,
            &format!(
                "optixModuleCreate: {}",
                log_text(&log[..size.min(log.len())])
            ),
        )?;

        let builtin = sys::OptixBuiltinISOptions {
            builtinISModuleType: sys::OptixPrimitiveType_OPTIX_PRIMITIVE_TYPE_SPHERE,
            usesMotionBlur: 1,
            buildFlags: sys::OptixBuildFlags_OPTIX_BUILD_FLAG_PREFER_FAST_TRACE as u32,
            ..Default::default()
        };
        let mut sphere_module = std::ptr::null_mut();
        check(
            unsafe {
                t.optixBuiltinISModuleGet.unwrap()(
                    optix.context,
                    &module_options,
                    &pipeline_options,
                    &builtin,
                    &mut sphere_module,
                )
            },
            "optixBuiltinISModuleGet",
        )?;

        let mut raygen = sys::OptixProgramGroupDesc {
            kind: sys::OptixProgramGroupKind_OPTIX_PROGRAM_GROUP_KIND_RAYGEN,
            ..Default::default()
        };
        raygen.__bindgen_anon_1.raygen = sys::OptixProgramGroupSingleModule {
            module,
            entryFunctionName: c"__raygen__segments".as_ptr(),
        };
        let mut miss = sys::OptixProgramGroupDesc {
            kind: sys::OptixProgramGroupKind_OPTIX_PROGRAM_GROUP_KIND_MISS,
            ..Default::default()
        };
        miss.__bindgen_anon_1.miss = sys::OptixProgramGroupSingleModule {
            module,
            entryFunctionName: c"__miss__none".as_ptr(),
        };
        let mut hit = sys::OptixProgramGroupDesc {
            kind: sys::OptixProgramGroupKind_OPTIX_PROGRAM_GROUP_KIND_HITGROUP,
            ..Default::default()
        };
        hit.__bindgen_anon_1.hitgroup = sys::OptixProgramGroupHitgroup {
            moduleAH: module,
            entryFunctionNameAH: c"__anyhit__swarm".as_ptr(),
            moduleIS: sphere_module,
            ..Default::default()
        };
        let descs = [raygen, miss, hit];
        let options = sys::OptixProgramGroupOptions::default();
        let mut groups = [std::ptr::null_mut(); 3];
        let mut size = log.len();
        let result = unsafe {
            t.optixProgramGroupCreate.unwrap()(
                optix.context,
                descs.as_ptr(),
                3,
                &options,
                log.as_mut_ptr().cast(),
                &mut size,
                groups.as_mut_ptr(),
            )
        };
        check(
            result,
            &format!(
                "optixProgramGroupCreate: {}",
                log_text(&log[..size.min(log.len())])
            ),
        )?;

        let link = sys::OptixPipelineLinkOptions {
            maxTraceDepth: 1,
            ..Default::default()
        };
        let mut pipeline = std::ptr::null_mut();
        let mut size = log.len();
        let result = unsafe {
            t.optixPipelineCreate.unwrap()(
                optix.context,
                &pipeline_options,
                &link,
                groups.as_ptr(),
                3,
                log.as_mut_ptr().cast(),
                &mut size,
                &mut pipeline,
            )
        };
        check(
            result,
            &format!(
                "optixPipelineCreate: {}",
                log_text(&log[..size.min(log.len())])
            ),
        )?;
        Ok(Self {
            optix,
            pipeline,
            groups,
        })
    }

    /// Builds a motion GAS of padded spheres for `bodies`. A ray at the step's mid
    /// time must reach every body the exact test could hit within ±STEP_SPAN / 2.
    fn build(
        &self,
        bodies: &[crate::swarm::GpuSwarmBody],
    ) -> (DeviceBuffer, u64, Vec<DeviceBuffer>, f32) {
        let t = &self.optix.table;
        let spacing = f64::from(TIME_END - TIME_BEGIN) / f64::from(KEYS - 1);
        let mut centres = Vec::new();
        let mut radii = Vec::new();
        let mut largest = 0.0_f32;
        for key in 0..KEYS {
            let time = f64::from(TIME_BEGIN) + spacing * f64::from(key);
            let (mut c, mut r) = (Vec::new(), Vec::new());
            for body in bodies {
                let p = body.center(time);
                c.push([p[0] as f32, p[1] as f32, p[2] as f32]);
                let orbit = f64::from(body.axis_a[3]);
                let omega = f64::from(body.orbit[1]).abs();
                let step_turn = omega * f64::from(STEP_SPAN);
                let key_turn = omega * spacing;
                // Motion over half a step, the step's own padding, and the gap
                // between the orbit and OptiX's linear interpolation between keys.
                let pad = orbit * omega * f64::from(STEP_SPAN) * 0.5
                    + 0.125 * orbit * step_turn * step_turn
                    + orbit * (1.0 - (0.5 * key_turn).cos())
                    + 0.01;
                r.push((f64::from(body.axis_b[3]) + pad) as f32);
                largest = largest.max(*r.last().unwrap());
            }
            centres.push(DeviceBuffer::from(&c));
            radii.push(DeviceBuffer::from(&r));
        }
        let centre_ptrs: Vec<u64> = centres.iter().map(|b| b.0).collect();
        let radius_ptrs: Vec<u64> = radii.iter().map(|b| b.0).collect();
        let flags = [sys::OptixGeometryFlags_OPTIX_GEOMETRY_FLAG_NONE as u32];
        let mut input = sys::OptixBuildInput {
            type_: sys::OptixBuildInputType_OPTIX_BUILD_INPUT_TYPE_SPHERES,
            ..Default::default()
        };
        input.__bindgen_anon_1.sphereArray = sys::OptixBuildInputSphereArray {
            vertexBuffers: centre_ptrs.as_ptr(),
            vertexStrideInBytes: 12,
            numVertices: bodies.len() as u32,
            radiusBuffers: radius_ptrs.as_ptr(),
            radiusStrideInBytes: 4,
            flags: flags.as_ptr(),
            numSbtRecords: 1,
            ..Default::default()
        };
        let options = sys::OptixAccelBuildOptions {
            buildFlags: sys::OptixBuildFlags_OPTIX_BUILD_FLAG_PREFER_FAST_TRACE as u32,
            operation: sys::OptixBuildOperation_OPTIX_BUILD_OPERATION_BUILD,
            motionOptions: sys::OptixMotionOptions {
                numKeys: KEYS,
                flags: 0,
                timeBegin: TIME_BEGIN,
                timeEnd: TIME_END,
            },
        };
        let mut sizes = sys::OptixAccelBufferSizes::default();
        check(
            unsafe {
                t.optixAccelComputeMemoryUsage.unwrap()(
                    self.optix.context,
                    &options,
                    &input,
                    1,
                    &mut sizes,
                )
            },
            "optixAccelComputeMemoryUsage",
        )
        .unwrap();
        let temp = DeviceBuffer::new(sizes.tempSizeInBytes);
        let output = DeviceBuffer::new(sizes.outputSizeInBytes);
        let mut handle = 0;
        let stream = shared_cuda().stream.cu_stream() as sys::CUstream;
        check(
            unsafe {
                t.optixAccelBuild.unwrap()(
                    self.optix.context,
                    stream,
                    &options,
                    &input,
                    1,
                    temp.0,
                    sizes.tempSizeInBytes,
                    output.0,
                    sizes.outputSizeInBytes,
                    &mut handle,
                    std::ptr::null(),
                    0,
                )
            },
            "optixAccelBuild",
        )
        .unwrap();
        shared_cuda().stream.synchronize().unwrap();
        centres.extend(radii);
        (output, handle, centres, 2.0 * largest + 0.01)
    }

    /// Hit colour and flag for each segment pair, as `bh_test_swarm_segment` returns.
    /// Also returns the launch time in milliseconds.
    #[cfg(test)]
    pub(crate) fn query(
        &self,
        segments: &[[f32; 4]],
        bodies: &[crate::swarm::GpuSwarmBody],
    ) -> (Vec<[f32; 4]>, f64) {
        let (_gas, handle, _keys, backoff) = self.build(bodies);
        let count = segments.len() / 2;
        let d_segments = DeviceBuffer::from(segments);
        let d_bodies = DeviceBuffer::from(bodies);
        let d_results = DeviceBuffer::new(count * 16);
        let queries = SegmentQueries {
            segments: d_segments.0,
            bodies: d_bodies.0,
            results: d_results.0,
            handle,
            count: count as u32,
            backoff,
        };
        let run = || {
            let _launch = self.launch(queries);
            shared_cuda().stream.synchronize().unwrap();
        };
        run();
        let start = std::time::Instant::now();
        run();
        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        let mut results = vec![[0.0_f32; 4]; count];
        unsafe { cudarc::driver::result::memcpy_dtoh_sync(&mut results, d_results.0).unwrap() };
        (results, elapsed)
    }

    /// Starts `queries` on the shared stream. The returned buffers hold the launch's
    /// parameters, so keep them until the stream has finished it.
    fn launch(&self, queries: SegmentQueries) -> [DeviceBuffer; 2] {
        let t = &self.optix.table;
        let count = queries.count;
        let queries = DeviceBuffer::from(&[queries]);
        let mut records = vec![0u8; 3 * SBT_RECORD];
        for (i, group) in self.groups.iter().enumerate() {
            let record = &mut records[i * SBT_RECORD..(i + 1) * SBT_RECORD];
            check(
                unsafe { t.optixSbtRecordPackHeader.unwrap()(*group, record.as_mut_ptr().cast()) },
                "optixSbtRecordPackHeader",
            )
            .unwrap();
            record[SBT_HEADER..SBT_HEADER + 8].copy_from_slice(&queries.0.to_le_bytes());
        }
        let d_records = DeviceBuffer::from(&records);
        let sbt = sys::OptixShaderBindingTable {
            raygenRecord: d_records.0,
            missRecordBase: d_records.0 + SBT_RECORD as u64,
            missRecordStrideInBytes: SBT_RECORD as u32,
            missRecordCount: 1,
            hitgroupRecordBase: d_records.0 + 2 * SBT_RECORD as u64,
            hitgroupRecordStrideInBytes: SBT_RECORD as u32,
            hitgroupRecordCount: 1,
            ..Default::default()
        };
        let stream = shared_cuda().stream.cu_stream() as sys::CUstream;
        check(
            unsafe { t.optixLaunch.unwrap()(self.pipeline, stream, 0, 0, &sbt, count, 1, 1) },
            "optixLaunch",
        )
        .unwrap();
        [queries, d_records]
    }
}

/// Device pointers and sizes for one swarm frame.
pub(crate) struct RenderInputs {
    pub out_image: u64,
    pub cam: u64,
    pub disk: u64,
    pub objects: u64,
    pub skybox: u64,
    pub size: (u32, u32, u32, u32),
    pub experiments: u32,
    pub cfg: LaunchConfig,
}

/// What one frame took, for benchmarks.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct RenderStats {
    /// Host time to build and upload the motion GAS, in ms.
    pub build_ms: f64,
    /// Steps the first pass queued for OptiX.
    pub queued: u32,
}

/// Queue entries (96 bytes each: the step, then the pixel state) per band.
const QUEUE_ENTRIES: u32 = (512 << 20) / 96;

/// The swarm renderer with RT-core queries, in three stages per band of rows:
/// `bh_geodesic_swarm_record` renders without the swarm and queues each step that
/// may meet it, one OptiX launch tests the queue, and `bh_swarm_first_hit` /
/// `bh_swarm_apply` redo the pixels whose earliest hit was a queued step. Bands
/// keep the queue within QUEUE_ENTRIES.
pub(crate) struct OptixRender {
    pipeline: SegmentPipeline,
    record: CudaFunction,
    first_hit: CudaFunction,
    apply: CudaFunction,
    queue: DeviceBuffer,
    states: DeviceBuffer,
    results: DeviceBuffer,
    pixels: usize,
    first: DeviceBuffer,
    counter: DeviceBuffer,
    /// The most queued steps per pixel in any band of the last frame.
    steps_per_pixel: f32,
}

// SAFETY: OptiX host calls are thread-safe, and Bevy gives one system at a time
// mutable access to the resource that owns this.
unsafe impl Send for OptixRender {}
unsafe impl Sync for OptixRender {}

impl OptixRender {
    pub(crate) fn new() -> Result<Self, String> {
        let module = &shared_cuda().module;
        let load = |name: &str| {
            module
                .load_function(name)
                .map_err(|e| format!("{name}: {e}"))
        };
        let entries = QUEUE_ENTRIES as usize;
        Ok(Self {
            pipeline: SegmentPipeline::new()?,
            record: load("bh_geodesic_swarm_record")?,
            first_hit: load("bh_swarm_first_hit")?,
            apply: load("bh_swarm_apply")?,
            queue: DeviceBuffer::new(entries * 32),
            states: DeviceBuffer::new(entries * 48),
            results: DeviceBuffer::new(entries * 16),
            pixels: 0,
            first: DeviceBuffer::new(0),
            counter: DeviceBuffer::new(4),
            steps_per_pixel: 100.0,
        })
    }

    /// Renders one frame into `inputs.out_image`.
    pub(crate) fn render(
        &mut self,
        inputs: &RenderInputs,
        bodies: &[crate::swarm::GpuSwarmBody],
    ) -> RenderStats {
        let cuda = shared_cuda();
        let stream = &cuda.stream;
        let start = std::time::Instant::now();
        let (_gas, handle, _keys, backoff) = self.pipeline.build(bodies);
        let build_ms = start.elapsed().as_secs_f64() * 1000.0;
        let (width, height, sky_w, sky_h) = inputs.size;
        let (belt_inner, belt_outer, belt_spread) = crate::swarm::swarm_belt(bodies);
        let pixels = (width * height) as usize;
        if self.pixels < pixels {
            self.first = DeviceBuffer::new(pixels * 4);
            self.pixels = pixels;
        }
        let d_bodies = DeviceBuffer::from(bodies);
        let body_count = bodies.len() as u32;
        let memset = |buffer: &DeviceBuffer, bytes: usize| unsafe {
            cudarc::driver::result::memset_d8_async(buffer.0, 0, bytes, stream.cu_stream()).unwrap()
        };
        let block_rows = inputs.cfg.block_dim.1;
        let mut densest = 0.0_f32;
        let mut queued_total = 0_u32;
        let mut row0 = 0;
        while row0 < height {
            // Whole blocks of rows, with headroom; a band that still overflows tests
            // the excess by brute force in the first pass.
            let fit = (QUEUE_ENTRIES as f32 / (1.25 * self.steps_per_pixel * width as f32)) as u32;
            let rows = (fit / block_rows).max(1) * block_rows;
            let rows = rows.min(height - row0);
            memset(&self.counter, 4);
            let cfg = LaunchConfig {
                grid_dim: (inputs.cfg.grid_dim.0, rows.div_ceil(block_rows), 1),
                ..inputs.cfg
            };
            let mut builder = stream.launch_builder(&self.record);
            builder
                .arg(&inputs.out_image)
                .arg(&inputs.cam)
                .arg(&inputs.disk)
                .arg(&inputs.objects)
                .arg(&inputs.skybox)
                .arg(&width)
                .arg(&height)
                .arg(&sky_w)
                .arg(&sky_h)
                .arg(&row0)
                .arg(&d_bodies.0)
                .arg(&body_count)
                .arg(&self.queue.0)
                .arg(&self.states.0)
                .arg(&self.counter.0)
                .arg(&QUEUE_ENTRIES)
                .arg(&belt_inner)
                .arg(&belt_outer)
                .arg(&belt_spread)
                .arg(&inputs.experiments);
            unsafe { builder.launch(cfg) }.expect("bh_geodesic_swarm_record launch failed");
            stream.synchronize().unwrap();
            let mut counted = [0u32];
            unsafe {
                cudarc::driver::result::memcpy_dtoh_sync(&mut counted, self.counter.0).unwrap()
            };
            densest = densest.max(counted[0] as f32 / (rows * width) as f32);
            self.steps_per_pixel = self.steps_per_pixel.max(densest);
            let queued = counted[0].min(QUEUE_ENTRIES);
            queued_total = queued_total.saturating_add(counted[0]);
            if queued > 0 {
                let _launch = self.pipeline.launch(SegmentQueries {
                    segments: self.queue.0,
                    bodies: d_bodies.0,
                    results: self.results.0,
                    handle,
                    count: queued,
                    backoff,
                });
                memset(&self.first, pixels * 4);
                let cfg = LaunchConfig::for_num_elems(queued);
                let mut builder = stream.launch_builder(&self.first_hit);
                builder
                    .arg(&self.results.0)
                    .arg(&self.states.0)
                    .arg(&self.first.0)
                    .arg(&queued);
                unsafe { builder.launch(cfg) }.expect("bh_swarm_first_hit launch failed");
                let mut builder = stream.launch_builder(&self.apply);
                builder
                    .arg(&inputs.out_image)
                    .arg(&inputs.cam)
                    .arg(&self.results.0)
                    .arg(&self.states.0)
                    .arg(&self.first.0)
                    .arg(&queued);
                unsafe { builder.launch(cfg) }.expect("bh_swarm_apply launch failed");
                // The next band reuses the queue, and the GAS is freed on return.
                stream.synchronize().unwrap();
            }
            row0 += rows;
        }
        self.steps_per_pixel = densest.max(1.0);
        RenderStats {
            build_ms,
            queued: queued_total,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::swarm::swarm_bodies;
    use cudarc::driver::{LaunchConfig, PushKernelArg};

    #[test]
    #[ignore = "requires an NVIDIA RTX driver and OPTIX_ROOT"]
    fn optix_context_starts() {
        let optix = Optix::new().unwrap();
        assert!(!optix.context.is_null());
        println!("OptiX ABI {} context ready", sys::OPTIX_ABI_VERSION);
    }

    /// Segments like the renderer's steps: within 12 r_g/c and inside the keyed window.
    fn segments(bodies: &[crate::swarm::GpuSwarmBody], count: usize) -> Vec<[f32; 4]> {
        let mut seed = 0x9e37_79b9_u64;
        let mut uniform = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed >> 11) as f64 / (1u64 << 53) as f64
        };
        let mut out = Vec::with_capacity(2 * count);
        for i in 0..count {
            let t0 = -390.0 * uniform();
            let start: [f64; 3] = if i % 2 == 0 {
                let c = bodies[(uniform() * bodies.len() as f64) as usize].center(t0);
                std::array::from_fn(|k| c[k] + 1.2 * (uniform() - 0.5))
            } else {
                [
                    90.0 * (uniform() - 0.5),
                    16.0 * (uniform() - 0.5),
                    90.0 * (uniform() - 0.5),
                ]
            };
            let dir: [f64; 3] = std::array::from_fn(|_| uniform() - 0.5);
            let norm = dir.iter().map(|v| v * v).sum::<f64>().sqrt();
            let length = 0.5 + 5.5 * uniform();
            let end: [f64; 3] = std::array::from_fn(|k| start[k] + length * dir[k] / norm);
            out.push([start[0] as f32, start[1] as f32, start[2] as f32, t0 as f32]);
            out.push([
                end[0] as f32,
                end[1] as f32,
                end[2] as f32,
                (t0 - length) as f32,
            ]);
        }
        out
    }

    fn brute_force(
        segments: &[[f32; 4]],
        bodies: &[crate::swarm::GpuSwarmBody],
    ) -> (Vec<[f32; 4]>, f64) {
        let cuda = shared_cuda();
        let count = (segments.len() / 2) as u32;
        let d_cases = cuda.clone_htod(segments);
        let d_bodies = cuda.clone_htod(bytemuck::cast_slice::<_, u8>(bodies));
        let mut d_results = cuda.alloc_zeros::<f32>(segments.len() * 2);
        let function = cuda.module.load_function("bh_test_swarm_segment").unwrap();
        let body_count = bodies.len() as u32;
        let mut elapsed = 0.0;
        for _ in 0..2 {
            let mut builder = cuda.stream.launch_builder(&function);
            builder.arg(&d_cases);
            builder.arg(&d_bodies);
            builder.arg(&body_count);
            builder.arg(&mut d_results);
            builder.arg(&count);
            cuda.stream.synchronize().unwrap();
            let start = std::time::Instant::now();
            unsafe { builder.launch(LaunchConfig::for_num_elems(count)).unwrap() };
            cuda.stream.synchronize().unwrap();
            elapsed = start.elapsed().as_secs_f64() * 1000.0;
        }
        let flat = cuda.clone_dtoh(&d_results);
        (flat.as_chunks::<4>().0.to_vec(), elapsed)
    }

    #[test]
    #[ignore = "requires an NVIDIA RTX driver and OPTIX_ROOT"]
    fn rt_core_queries_match_brute_force() {
        let pipeline = SegmentPipeline::new().unwrap();
        for count in [1024u32, 4096, 16384] {
            let bodies = swarm_bodies(count, 0.82, 1234.5);
            let cases = segments(&bodies, 200_000);
            let (expected, brute_ms) = brute_force(&cases, &bodies);
            let build = std::time::Instant::now();
            let (actual, optix_ms) = pipeline.query(&cases, &bodies);
            let total = build.elapsed().as_secs_f64() * 1000.0;
            let hits = expected.iter().filter(|r| r[3] > 0.0).count();
            let differing = expected
                .iter()
                .zip(&actual)
                .filter(|(a, b)| a.map(f32::to_bits) != b.map(f32::to_bits))
                .count();
            println!(
                "{count:>6} bodies: 200k segments, {hits} hits; brute force {brute_ms:.2} ms, \
                 OptiX {optix_ms:.2} ms (with GAS build and setup {total:.1} ms); {differing} differ"
            );
            assert_eq!(differing, 0);
        }
    }
}
