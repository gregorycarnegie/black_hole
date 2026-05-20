// Temporal accumulation: blends the current geodesic frame into a running
// average stored in a ping-pong rgba32float buffer.
//
// Bindings (see accumulate.rs for the layout):
//   0 – display      : rgba8unorm  write — what the sprite shows
//   1 – new_frame    : texture_2d  read  — raw output of geodesic.wgsl
//   2 – prev_accum   : texture_2d  read  — previous history buffer
//   3 – curr_accum   : rgba32float write — history buffer being written
//   4 – blend params : uniform

@group(0) @binding(0) var display:    texture_storage_2d<rgba8unorm,  write>;
@group(0) @binding(1) var new_frame:  texture_2d<f32>;
@group(0) @binding(2) var prev_accum: texture_2d<f32>;
@group(0) @binding(3) var curr_accum: texture_storage_2d<rgba32float, write>;

struct BlendParams {
    frame_count: u32,
    _pad0: u32,
    _pad1: u32,
    _pad2: u32,
}
@group(0) @binding(4) var<uniform> blend: BlendParams;

@compute @workgroup_size(16, 16, 1)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let dims = textureDimensions(display);
    let pix  = vec2<i32>(i32(gid.x), i32(gid.y));
    if pix.x >= i32(dims.x) || pix.y >= i32(dims.y) { return; }

    let new_c = textureLoad(new_frame, pix, 0);

    var out: vec4<f32>;
    if blend.frame_count == 0u {
        // First still frame (or any moving frame): reset history.
        out = new_c;
    } else {
        let prev = textureLoad(prev_accum, pix, 0);
        // Exponential moving average — converges in ~10 frames.
        out = mix(prev, new_c, 0.1);
    }

    textureStore(curr_accum, pix, out);
    textureStore(display,    pix, out);
}
