// OptiX programs for swarm segment queries, compiled by cuda-oxide alongside the
// CUDA kernels so they share `swarm_body_hit`. Intrinsics are the inline PTX calls
// that OptiX's own device headers emit.

/// Read through the SBT record data of every program. Matches `SegmentQueries`
/// in `src/compute/optix.rs`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SegmentQueries {
    /// Pairs (start, t0), (end, t1).
    pub segments: *const Vec4,
    pub bodies: *const SwarmBody,
    /// Hit colour and flag, as from `bh_test_swarm_segment`.
    pub results: *mut Vec4,
    pub handle: u64,
    pub count: u32,
    /// Twice the largest padded radius: rays start this far behind each segment,
    /// outside every sphere the segment touches.
    pub backoff: f32,
}

#[inline(always)]
fn sbt_queries() -> &'static SegmentQueries {
    let pointer: u64;
    unsafe {
        cuda_device::ptx_asm!("call (%0), _optix_get_sbt_data_ptr_64, ();", out("=l") pointer);
        // The record's data holds a pointer to the shared queries.
        &**(pointer as *const *const SegmentQueries)
    }
}

#[inline(always)]
fn launch_index_x() -> u32 {
    let index: u32;
    unsafe { cuda_device::ptx_asm!("call (%0), _optix_get_launch_index_x, ();", out("=r") index) };
    index
}

#[inline(always)]
fn get_payload(slot: u32) -> u32 {
    let value: u32;
    unsafe {
        cuda_device::ptx_asm!("call (%0), _optix_get_payload, (%1);", out("=r") value, in("r") slot)
    };
    value
}

#[inline(always)]
fn set_payload(slot: u32, value: u32) {
    unsafe { cuda_device::ptx_asm!("call _optix_set_payload, (%0, %1);", in("r") slot, in("r") value) };
}

#[inline(always)]
fn primitive_index() -> u32 {
    let index: u32;
    unsafe { cuda_device::ptx_asm!("call (%0), _optix_read_primitive_idx, ();", out("=r") index) };
    index
}

/// `optixTrace` with three payload values; the third is passed in only.
#[inline(always)]
fn trace3(handle: u64, origin: Vec3, direction: Vec3, tmax: f32, time: f32, p: [u32; 3]) -> (u32, u32) {
    let (p0, p1): (u32, u32);
    unsafe {
        cuda_device::ptx_asm!(
            "{ .reg .b32 %%z, %%t, %%m, %%f, %%o, %%s, %%n, %%c, %%d<30>; .reg .f32 %%lo;
              mov.b32 %%z, 0; mov.b32 %%t, 0; mov.b32 %%m, 255; mov.b32 %%f, 0; mov.b32 %%o, 0;
              mov.b32 %%s, 1; mov.b32 %%n, 0; mov.b32 %%c, 3; mov.f32 %%lo, 0f00000000;
              call (%0, %1, %%d0, %%d1, %%d2, %%d3, %%d4, %%d5, %%d6, %%d7, %%d8, %%d9, %%d10, %%d11,
                    %%d12, %%d13, %%d14, %%d15, %%d16, %%d17, %%d18, %%d19, %%d20, %%d21, %%d22, %%d23,
                    %%d24, %%d25, %%d26, %%d27, %%d28, %%d29),
                   _optix_trace_typed_32,
                   (%%t, %2, %3, %4, %5, %6, %7, %8, %%lo, %9, %10, %%m, %%f, %%o, %%s, %%n, %%c,
                    %11, %12, %13, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z,
                    %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z, %%z); }",
            out("=r") p0,
            out("=r") p1,
            in("l") handle,
            in("f") origin.x,
            in("f") origin.y,
            in("f") origin.z,
            in("f") direction.x,
            in("f") direction.y,
            in("f") direction.z,
            in("f") tmax,
            in("f") time,
            in("r") p[0],
            in("r") p[1],
            in("r") p[2],
        );
    }
    (p0, p1)
}

/// One straight ray per segment at the segment's mid time; the any-hit program
/// applies the exact space-time test to every candidate the hardware reports.
#[cuda_device::kernel]
pub unsafe fn __raygen__segments() {
    let q = sbt_queries();
    let i = launch_index_x();
    if i >= q.count {
        return;
    }
    let a = unsafe { *q.segments.add(2 * i as usize) };
    let b = unsafe { *q.segments.add(2 * i as usize + 1) };
    let d = b.xyz() - a.xyz();
    let length = d.length().max(1.0e-12);
    let direction = d / length;
    let (_, body) = trace3(
        q.handle,
        a.xyz() - q.backoff * direction,
        direction,
        length + q.backoff,
        0.5 * (a.w + b.w),
        [2.0_f32.to_bits(), u32::MAX, i],
    );
    let mut result = vec4_splat(0.0);
    if body != u32::MAX {
        let mut best = 2.0_f32;
        swarm_body_hit(
            swarm_query(a.xyz(), b.xyz(), a.w, b.w),
            unsafe { *q.bodies.add(body as usize) },
            &mut best,
            &mut result,
        );
    }
    unsafe { *q.results.add(i as usize) = result };
}

/// Keeps the earliest exact hit, preferring the lower body index on ties as the
/// brute-force loop does, and ignores every candidate so traversal continues.
#[cuda_device::kernel]
pub unsafe fn __anyhit__swarm() {
    let q = sbt_queries();
    keep_earliest_hit(q.segments, q.bodies);
}

/// The any-hit work: payload 2 indexes the segment pair in `segments`.
#[inline(always)]
fn keep_earliest_hit(segments: *const Vec4, bodies: *const SwarmBody) {
    let q_bodies = bodies;
    let segment = get_payload(2);
    let a = unsafe { *segments.add(2 * segment as usize) };
    let b = unsafe { *segments.add(2 * segment as usize + 1) };
    let body = primitive_index();
    let mut s = 2.0_f32;
    let mut colour = vec4_splat(0.0);
    swarm_body_hit(
        swarm_query(a.xyz(), b.xyz(), a.w, b.w),
        unsafe { *q_bodies.add(body as usize) },
        &mut s,
        &mut colour,
    );
    let best = f32::from_bits(get_payload(0));
    if colour.w > 0.0 && (s < best || (s == best && body < get_payload(1))) {
        set_payload(0, s.to_bits());
        set_payload(1, body);
    }
    unsafe { cuda_device::ptx_asm!("call _optix_ignore_intersection, ();") };
}

#[cuda_device::kernel]
pub unsafe fn __miss__none() {}

/// The production renderer with RT-core swarm queries. Matches `RenderParams` in
/// `src/compute/optix.rs`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct RenderParams {
    pub out_image: *mut Vec4,
    pub cam: *const Camera,
    pub disk: *const Disk,
    pub objects: *const Objects,
    pub skybox: *const Vec4,
    pub bodies: *const SwarmBody,
    /// Two Vec4s per pixel: the step the any-hit program tests.
    pub scratch: *mut Vec4,
    pub handle: u64,
    pub width: u32,
    pub height: u32,
    pub sky_w: u32,
    pub sky_h: u32,
    pub body_count: u32,
    pub experiments: u32,
    pub backoff: f32,
    /// Radial shell holding every body's padded orbit: steps outside it cannot hit.
    pub belt_inner: f32,
    pub belt_outer: f32,
    pub _pad: u32,
}

#[inline(always)]
fn sbt_render() -> &'static RenderParams {
    let pointer: u64;
    unsafe {
        cuda_device::ptx_asm!("call (%0), _optix_get_sbt_data_ptr_64, ();", out("=l") pointer);
        &**(pointer as *const *const RenderParams)
    }
}

#[inline(always)]
fn launch_index_y() -> u32 {
    let index: u32;
    unsafe { cuda_device::ptx_asm!("call (%0), _optix_get_launch_index_y, ();", out("=r") index) };
    index
}

/// Same results as `swarm_bvh_hit`: steps the BVH would send to brute force go
/// there too; the rest trace one ray at the step's mid time.
#[inline(always)]
fn optix_swarm_hit(q: &RenderParams, slot: u32, start: Vec3, end: Vec3, t0: f32, t1: f32) -> Vec4 {
    let middle = -0.5 * (t0 + t1);
    if !(middle >= 0.0
        && (t0 - t1).abs() <= SWARM_STEP_SPAN
        && middle < SWARM_SLICE_WIDTH * SWARM_SLICES)
    {
        return swarm_segment_hit(start, end, t0, t1, q.bodies, q.body_count);
    }
    // Every body's own radial test would reject this step, so skip the trace.
    let shell = swarm_query(start, end, t0, t1);
    if shell.far_r < q.belt_inner || shell.near_r > q.belt_outer {
        return vec4_splat(0.0);
    }
    unsafe {
        *q.scratch.add(2 * slot as usize) = vec4_v3_f(start, t0);
        *q.scratch.add(2 * slot as usize + 1) = vec4_v3_f(end, t1);
    }
    let d = end - start;
    let length = d.length().max(1.0e-12);
    let direction = d / length;
    let (_, body) = trace3(
        q.handle,
        start - q.backoff * direction,
        direction,
        length + q.backoff,
        -middle,
        [2.0_f32.to_bits(), u32::MAX, slot],
    );
    let mut result = vec4_splat(0.0);
    if body != u32::MAX {
        let mut best = 2.0_f32;
        swarm_body_hit(
            swarm_query(start, end, t0, t1),
            unsafe { *q.bodies.add(body as usize) },
            &mut best,
            &mut result,
        );
    }
    result
}

#[cuda_device::kernel]
pub unsafe fn __raygen__render() {
    let q = sbt_render();
    let (x, y) = (launch_index_x(), launch_index_y());
    let slot = y * q.width + x;
    unsafe {
        render_geodesic::<false, true, _>(
            q.out_image, q.cam, q.disk, q.objects, q.skybox, q.width, q.height, q.sky_w, q.sky_h,
            core::ptr::null_mut(), q.experiments & 1 != 0, q.experiments & 2 != 0, x, y,
            |start, end, t0, t1| optix_swarm_hit(q, slot, start, end, t0, t1),
        );
    }
}

#[cuda_device::kernel]
pub unsafe fn __anyhit__render() {
    let q = sbt_render();
    keep_earliest_hit(q.scratch, q.bodies);
}
