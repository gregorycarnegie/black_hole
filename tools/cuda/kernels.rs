// CUDA device kernels and physics helpers compiled to PTX by `cuda-oxide`.

use core::ops::{
    Add, AddAssign, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, Sub, SubAssign,
};

mod ellis {
    include!("../../src/ellis.rs");
}

// -- Thread indexing & scalar math intrinsics --------------------------------

#[inline(always)]
fn gid_x() -> u32 {
    cuda_device::thread::blockIdx_x() * cuda_device::thread::blockDim_x()
        + cuda_device::thread::threadIdx_x()
}

#[inline(always)]
fn gid_y() -> u32 {
    cuda_device::thread::blockIdx_y() * cuda_device::thread::blockDim_y()
        + cuda_device::thread::threadIdx_y()
}

#[inline(always)]
fn sqrt(x: f32) -> f32 {
    cuda_device::float::sqrt_rn_f32(x)
}

#[inline(always)]
fn inverse_sqrt(x: f32) -> f32 {
    1.0 / cuda_device::float::sqrt_rn_f32(x)
}

#[inline(always)]
fn clamp_f32(x: f32, lo: f32, hi: f32) -> f32 {
    x.max(lo).min(hi)
}

#[inline(always)]
fn round_even(x: f32) -> f32 {
    const MAGIC: f32 = 8_388_608.0;
    if x.abs() < MAGIC {
        if x >= 0.0 {
            cuda_device::float::add_rn_f32(cuda_device::float::add_rn_f32(x, MAGIC), -MAGIC)
        } else {
            cuda_device::float::add_rn_f32(cuda_device::float::add_rn_f32(x, -MAGIC), MAGIC)
        }
    } else {
        x
    }
}

#[inline(always)]
fn floor_f32(x: f32) -> f32 {
    if x.abs() < 8_388_608.0 {
        let t = (x as i32) as f32;
        if x < t { t - 1.0 } else { t }
    } else {
        x
    }
}

#[inline(always)]
fn fract_f32(x: f32) -> f32 {
    x - floor_f32(x)
}

#[inline(always)]
fn exp(x: f32) -> f32 {
    if x >= 88.722_84_f32 {
        return f32::INFINITY;
    }
    if x <= -103.972_08_f32 {
        return 0.0;
    }
    const LOG2_E: f32 = 1.442_695_040_888_963_4;
    const LN2_HI: f32 = 0.693_145_751_953_125;
    const LN2_LO: f32 = 1.428_606_765_330_187e-6;
    let k = round_even(x * LOG2_E);
    let r = (x - k * LN2_HI) - k * LN2_LO;
    let p = 1.0
        + r * (1.0
            + r * (0.5
                + r * ((1.0 / 6.0)
                    + r * ((1.0 / 24.0) + r * ((1.0 / 120.0) + r * (1.0 / 720.0))))));
    p * cuda_device::float::ex2_approx_f32(k)
}

#[inline(always)]
fn log(x: f32) -> f32 {
    if !(x > 0.0) {
        return if x == 0.0 {
            f32::NEG_INFINITY
        } else {
            f32::NAN
        };
    }
    if x == f32::INFINITY {
        return f32::INFINITY;
    }
    let mut val = x;
    let mut exp_adjust = 0i32;
    if val < f32::MIN_POSITIVE {
        val *= 8_388_608.0;
        exp_adjust = -23;
    }
    let bits = val.to_bits();
    let mut e = ((bits >> 23) & 0xff) as i32 - 127 + exp_adjust;
    let mut m = f32::from_bits((bits & 0x007f_ffff) | 0x3f80_0000);
    if m > 1.414_213_56_f32 {
        m *= 0.5;
        e += 1;
    }
    let u = (m - 1.0) / (m + 1.0);
    let u2 = u * u;
    let ln_m = 2.0
        * u
        * (1.0
            + u2 * ((1.0 / 3.0)
                + u2 * ((1.0 / 5.0)
                    + u2 * ((1.0 / 7.0) + u2 * ((1.0 / 9.0) + u2 * (1.0 / 11.0))))));
    const LN2_HI: f32 = 0.693_145_751_953_125;
    const LN2_LO: f32 = 1.428_606_765_330_187e-6;
    let ef = e as f32;
    ef * LN2_HI + (ef * LN2_LO + ln_m)
}

#[inline(always)]
fn pow(x: f32, y: f32) -> f32 {
    if x <= 0.0 {
        return 0.0;
    }
    exp(y * log(x))
}

#[inline(always)]
fn tanh(x: f32) -> f32 {
    let ax = x.abs();
    if ax < 1.0e-3 {
        return x;
    }
    let clamped = ax.min(20.0);
    let e = exp(-2.0 * clamped);
    let t = (1.0 - e) / (1.0 + e);
    if x < 0.0 { -t } else { t }
}

#[inline(always)]
fn smoothstep(edge0: f32, edge1: f32, x: f32) -> f32 {
    let t = clamp_f32((x - edge0) / (edge1 - edge0), 0.0, 1.0);
    t * t * (3.0 - 2.0 * t)
}

#[inline(always)]
fn sin(x: f32) -> f32 {
    sincos(x).x
}

#[inline(always)]
fn cos(x: f32) -> f32 {
    sincos(x).y
}

// -- Vector and matrix types -------------------------------------------------

#[repr(C)]
#[derive(Clone, Copy, Default, PartialEq)]
pub struct Vec2 {
    pub x: f32,
    pub y: f32,
}

#[repr(C)]
#[derive(Clone, Copy, Default, PartialEq)]
pub struct Vec3 {
    pub x: f32,
    pub y: f32,
    pub z: f32,
}

#[repr(C)]
#[derive(Clone, Copy, Default, PartialEq)]
pub struct Vec4 {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub w: f32,
}

#[repr(C)]
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct UVec3 {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct Mat3 {
    pub cols: [Vec3; 3],
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct Mat4 {
    pub cols: [Vec4; 4],
}

#[inline(always)]
const fn vec2(x: f32, y: f32) -> Vec2 {
    Vec2 { x, y }
}

#[inline(always)]
const fn vec2_splat(v: f32) -> Vec2 {
    Vec2 { x: v, y: v }
}

#[inline(always)]
const fn vec3(x: f32, y: f32, z: f32) -> Vec3 {
    Vec3 { x, y, z }
}

#[inline(always)]
const fn vec3_splat(v: f32) -> Vec3 {
    Vec3 { x: v, y: v, z: v }
}

#[inline(always)]
const fn vec4(x: f32, y: f32, z: f32, w: f32) -> Vec4 {
    Vec4 { x, y, z, w }
}

#[inline(always)]
const fn vec4_splat(v: f32) -> Vec4 {
    Vec4 {
        x: v,
        y: v,
        z: v,
        w: v,
    }
}

#[inline(always)]
const fn vec4_f_v3(x: f32, v: Vec3) -> Vec4 {
    Vec4 {
        x,
        y: v.x,
        z: v.y,
        w: v.z,
    }
}

#[inline(always)]
const fn vec4_v3_f(v: Vec3, w: f32) -> Vec4 {
    Vec4 {
        x: v.x,
        y: v.y,
        z: v.z,
        w,
    }
}

#[inline(always)]
const fn vec4_f_v2_f(x: f32, v: Vec2, w: f32) -> Vec4 {
    Vec4 {
        x,
        y: v.x,
        z: v.y,
        w,
    }
}

#[inline(always)]
const fn vec3_v2_f(v: Vec2, z: f32) -> Vec3 {
    Vec3 {
        x: v.x,
        y: v.y,
        z,
    }
}

#[inline(always)]
const fn uvec3(x: u32, y: u32, z: u32) -> UVec3 {
    UVec3 { x, y, z }
}

#[inline(always)]
const fn mat3(c0: Vec3, c1: Vec3, c2: Vec3) -> Mat3 {
    Mat3 { cols: [c0, c1, c2] }
}

#[inline(always)]
const fn mat4(c0: Vec4, c1: Vec4, c2: Vec4, c3: Vec4) -> Mat4 {
    Mat4 {
        cols: [c0, c1, c2, c3],
    }
}

impl Vec2 {
    #[inline(always)]
    fn dot(self, rhs: Self) -> f32 {
        self.x * rhs.x + self.y * rhs.y
    }
    #[inline(always)]
    fn length(self) -> f32 {
        sqrt(self.dot(self))
    }
    #[inline(always)]
    fn mix(self, other: Self, t: f32) -> Self {
        self * (1.0 - t) + other * t
    }
}

impl Vec3 {
    #[inline(always)]
    fn xz(self) -> Vec2 {
        vec2(self.x, self.z)
    }
    #[inline(always)]
    fn xy(self) -> Vec2 {
        vec2(self.x, self.y)
    }
    #[inline(always)]
    fn dot(self, rhs: Self) -> f32 {
        self.x * rhs.x + self.y * rhs.y + self.z * rhs.z
    }
    #[inline(always)]
    fn cross(self, rhs: Self) -> Self {
        vec3(
            self.y * rhs.z - self.z * rhs.y,
            self.z * rhs.x - self.x * rhs.z,
            self.x * rhs.y - self.y * rhs.x,
        )
    }
    #[inline(always)]
    fn length(self) -> f32 {
        sqrt(self.dot(self))
    }
    #[inline(always)]
    fn normalize(self) -> Self {
        self * inverse_sqrt(self.dot(self))
    }
    #[inline(always)]
    fn abs(self) -> Self {
        vec3(self.x.abs(), self.y.abs(), self.z.abs())
    }
    #[inline(always)]
    fn floor(self) -> Self {
        vec3(floor_f32(self.x), floor_f32(self.y), floor_f32(self.z))
    }
    #[inline(always)]
    fn clamp(self, lo: Self, hi: Self) -> Self {
        vec3(
            clamp_f32(self.x, lo.x, hi.x),
            clamp_f32(self.y, lo.y, hi.y),
            clamp_f32(self.z, lo.z, hi.z),
        )
    }
    #[inline(always)]
    fn mix(self, other: Self, t: f32) -> Self {
        self * (1.0 - t) + other * t
    }
    #[inline(always)]
    fn all_lt(self, bound: f32) -> bool {
        self.x < bound && self.y < bound && self.z < bound
    }
    #[inline(always)]
    fn all_le(self, bound: f32) -> bool {
        self.x <= bound && self.y <= bound && self.z <= bound
    }
}

impl Vec4 {
    #[inline(always)]
    fn xyz(self) -> Vec3 {
        vec3(self.x, self.y, self.z)
    }
    #[inline(always)]
    fn yzw(self) -> Vec3 {
        vec3(self.y, self.z, self.w)
    }
    #[inline(always)]
    fn dot(self, rhs: Self) -> f32 {
        self.x * rhs.x + self.y * rhs.y + self.z * rhs.z + self.w * rhs.w
    }
    #[inline(always)]
    fn length(self) -> f32 {
        sqrt(self.dot(self))
    }
    #[inline(always)]
    fn abs(self) -> Self {
        vec4(self.x.abs(), self.y.abs(), self.z.abs(), self.w.abs())
    }
    #[inline(always)]
    fn max(self, rhs: Self) -> Self {
        vec4(
            self.x.max(rhs.x),
            self.y.max(rhs.y),
            self.z.max(rhs.z),
            self.w.max(rhs.w),
        )
    }
    #[inline(always)]
    fn mix(self, other: Self, t: f32) -> Self {
        self * (1.0 - t) + other * t
    }
    #[inline(always)]
    fn all_lt(self, bound: f32) -> bool {
        self.x < bound && self.y < bound && self.z < bound && self.w < bound
    }
}

impl Index<u32> for Vec3 {
    type Output = f32;
    #[inline(always)]
    fn index(&self, index: u32) -> &f32 {
        match index {
            0 => &self.x,
            1 => &self.y,
            _ => &self.z,
        }
    }
}

impl IndexMut<u32> for Vec3 {
    #[inline(always)]
    fn index_mut(&mut self, index: u32) -> &mut f32 {
        match index {
            0 => &mut self.x,
            1 => &mut self.y,
            _ => &mut self.z,
        }
    }
}

impl Index<u32> for Vec4 {
    type Output = f32;
    #[inline(always)]
    fn index(&self, index: u32) -> &f32 {
        match index {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            _ => &self.w,
        }
    }
}

impl IndexMut<u32> for Vec4 {
    #[inline(always)]
    fn index_mut(&mut self, index: u32) -> &mut f32 {
        match index {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            _ => &mut self.w,
        }
    }
}

impl Index<u32> for Mat3 {
    type Output = Vec3;
    #[inline(always)]
    fn index(&self, index: u32) -> &Vec3 {
        &self.cols[index as usize]
    }
}

impl IndexMut<u32> for Mat3 {
    #[inline(always)]
    fn index_mut(&mut self, index: u32) -> &mut Vec3 {
        &mut self.cols[index as usize]
    }
}

impl Index<u32> for Mat4 {
    type Output = Vec4;
    #[inline(always)]
    fn index(&self, index: u32) -> &Vec4 {
        &self.cols[index as usize]
    }
}

impl IndexMut<u32> for Mat4 {
    #[inline(always)]
    fn index_mut(&mut self, index: u32) -> &mut Vec4 {
        &mut self.cols[index as usize]
    }
}

macro_rules! impl_vec_ops {
    ($t:ident, $($f:ident),+) => {
        impl Add for $t {
            type Output = Self;
            #[inline(always)]
            fn add(self, rhs: Self) -> Self {
                Self { $($f: self.$f + rhs.$f),+ }
            }
        }
        impl AddAssign for $t {
            #[inline(always)]
            fn add_assign(&mut self, rhs: Self) {
                $(self.$f += rhs.$f;)+
            }
        }
        impl Sub for $t {
            type Output = Self;
            #[inline(always)]
            fn sub(self, rhs: Self) -> Self {
                Self { $($f: self.$f - rhs.$f),+ }
            }
        }
        impl SubAssign for $t {
            #[inline(always)]
            fn sub_assign(&mut self, rhs: Self) {
                $(self.$f -= rhs.$f;)+
            }
        }
        impl Mul for $t {
            type Output = Self;
            #[inline(always)]
            fn mul(self, rhs: Self) -> Self {
                Self { $($f: self.$f * rhs.$f),+ }
            }
        }
        impl Mul<f32> for $t {
            type Output = Self;
            #[inline(always)]
            fn mul(self, rhs: f32) -> Self {
                Self { $($f: self.$f * rhs),+ }
            }
        }
        impl Mul<$t> for f32 {
            type Output = $t;
            #[inline(always)]
            fn mul(self, rhs: $t) -> $t {
                $t { $($f: self * rhs.$f),+ }
            }
        }
        impl MulAssign<f32> for $t {
            #[inline(always)]
            fn mul_assign(&mut self, rhs: f32) {
                $(self.$f *= rhs;)+
            }
        }
        impl Div for $t {
            type Output = Self;
            #[inline(always)]
            fn div(self, rhs: Self) -> Self {
                Self { $($f: self.$f / rhs.$f),+ }
            }
        }
        impl Div<f32> for $t {
            type Output = Self;
            #[inline(always)]
            fn div(self, rhs: f32) -> Self {
                Self { $($f: self.$f / rhs),+ }
            }
        }
        impl DivAssign<f32> for $t {
            #[inline(always)]
            fn div_assign(&mut self, rhs: f32) {
                $(self.$f /= rhs;)+
            }
        }
        impl Neg for $t {
            type Output = Self;
            #[inline(always)]
            fn neg(self) -> Self {
                Self { $($f: -self.$f),+ }
            }
        }
    };
}

impl_vec_ops!(Vec2, x, y);
impl_vec_ops!(Vec3, x, y, z);
impl_vec_ops!(Vec4, x, y, z, w);

impl Add for UVec3 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        uvec3(self.x + rhs.x, self.y + rhs.y, self.z + rhs.z)
    }
}

impl Add for Mat3 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        mat3(
            self.cols[0] + rhs.cols[0],
            self.cols[1] + rhs.cols[1],
            self.cols[2] + rhs.cols[2],
        )
    }
}

impl Mul<f32> for Mat3 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: f32) -> Self {
        mat3(self.cols[0] * rhs, self.cols[1] * rhs, self.cols[2] * rhs)
    }
}

impl Mul<Mat3> for f32 {
    type Output = Mat3;
    #[inline(always)]
    fn mul(self, rhs: Mat3) -> Mat3 {
        rhs * self
    }
}

impl Mul<Vec3> for Mat3 {
    type Output = Vec3;
    #[inline(always)]
    fn mul(self, v: Vec3) -> Vec3 {
        self.cols[0] * v.x + self.cols[1] * v.y + self.cols[2] * v.z
    }
}

impl Mul<Mat3> for Mat3 {
    type Output = Mat3;
    #[inline(always)]
    fn mul(self, rhs: Mat3) -> Mat3 {
        mat3(
            self * rhs.cols[0],
            self * rhs.cols[1],
            self * rhs.cols[2],
        )
    }
}

impl Add for Mat4 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        mat4(
            self.cols[0] + rhs.cols[0],
            self.cols[1] + rhs.cols[1],
            self.cols[2] + rhs.cols[2],
            self.cols[3] + rhs.cols[3],
        )
    }
}

impl AddAssign for Mat4 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for Mat4 {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        mat4(
            self.cols[0] - rhs.cols[0],
            self.cols[1] - rhs.cols[1],
            self.cols[2] - rhs.cols[2],
            self.cols[3] - rhs.cols[3],
        )
    }
}

impl SubAssign for Mat4 {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul<f32> for Mat4 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: f32) -> Self {
        mat4(
            self.cols[0] * rhs,
            self.cols[1] * rhs,
            self.cols[2] * rhs,
            self.cols[3] * rhs,
        )
    }
}

impl Mul<Mat4> for f32 {
    type Output = Mat4;
    #[inline(always)]
    fn mul(self, rhs: Mat4) -> Mat4 {
        rhs * self
    }
}

impl Mul<Vec4> for Mat4 {
    type Output = Vec4;
    #[inline(always)]
    fn mul(self, v: Vec4) -> Vec4 {
        self.cols[0] * v.x + self.cols[1] * v.y + self.cols[2] * v.z + self.cols[3] * v.w
    }
}

impl Mul<Mat4> for Mat4 {
    type Output = Mat4;
    #[inline(always)]
    fn mul(self, rhs: Mat4) -> Mat4 {
        mat4(
            self * rhs.cols[0],
            self * rhs.cols[1],
            self * rhs.cols[2],
            self * rhs.cols[3],
        )
    }
}

// -- Host/Device ABI structs -------------------------------------------------

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Camera {
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
    pub debug_heatmap: u32,
    pub max_iter: u32,
    pub polarization_view: u32,
    pub frequency_ghz: f32,
    pub faraday_depth: f32,
    pub conversion_depth: f32,
    pub wormhole_radius: f32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Disk {
    pub r1: f32,
    pub r2: f32,
    pub h_thin: f32,
    pub h_hot: f32,
    pub spin: f32,
    pub horizon_r: f32,
    pub isco_r: f32,
    pub r_trunc: f32,
    pub tilt_deg: f32,
    pub r_bp: f32,
    pub twist_deg: f32,
    pub model: u32,
    pub binary_enabled: u32,
    pub _pad0: f32,
    pub _pad1: f32,
    pub _pad2: f32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Objects {
    pub num_objects: i32,
    pub _pad0: f32,
    pub _pad1: f32,
    pub _pad2: f32,
    pub pos_radius: [Vec4; 16],
    pub color: [Vec4; 16],
    pub mass: [Vec4; 16],
    pub spin: [Vec4; 16],
}

/// A massless body on a prescribed circular orbit about the origin.
/// Position at camera-relative coordinate time `t`:
/// `axis_a.w * (cos(orbit.x + orbit.y t) axis_a.xyz + sin(orbit.x + orbit.y t) axis_b.xyz)`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SwarmBody {
    /// Orbital axis at phase 0, then orbit radius.
    pub axis_a: Vec4,
    /// Direction of motion at phase 0, then body radius.
    pub axis_b: Vec4,
    /// Phase at the camera time, angular velocity, albedo, unused.
    pub orbit: Vec4,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SnapshotHeader {
    pub start: Vec4,
    pub spacing: Vec4,
    pub grid: Vec4,
    pub geometry: Vec4,
    pub physical: Vec4,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct ImageSeed {
    pub position: Vec4,
    pub momentum: Vec4,
    pub screen: Vec4,
    pub jones: Vec4,
}

// -- Constants ---------------------------------------------------------------

const PI: f32 = 3.141592653589793;
const SQRT3_2: f32 = 0.8660254037844386;
const SCHWARZSCHILD_RADIUS: f32 = 2.0;
const ESCAPE_R: f32 = 1600.0;
const STEP_TOLERANCE: f32 = 5.0e-8;

const ETA: Mat4 = mat4(
    vec4(-1.0, 0.0, 0.0, 0.0),
    vec4(0.0, 1.0, 0.0, 0.0),
    vec4(0.0, 0.0, 1.0, 0.0),
    vec4(0.0, 0.0, 0.0, 1.0),
);

const IDENTITY4: Mat4 = mat4(
    vec4(1.0, 0.0, 0.0, 0.0),
    vec4(0.0, 1.0, 0.0, 0.0),
    vec4(0.0, 0.0, 1.0, 0.0),
    vec4(0.0, 0.0, 0.0, 1.0),
);

// -- Polarized transfer -------------------------------------------------------

#[derive(Clone, Copy, Default)]
pub struct TransferCoefficients {
    pub emission: Vec4,
    pub absorption: Vec4,
    pub faraday: Vec3,
}

#[derive(Clone, Copy, Default)]
pub struct TransferResult {
    pub stokes: Vec4,
    pub transmission: Mat4,
    pub valid: bool,
}

#[cuda_device::device]
fn transfer_cell(initial: Vec4, c: TransferCoefficients, ds: f32) -> TransferResult {
    let mut result = TransferResult::default();
    if !(ds >= 0.0 && ds < 1.0e10)
        || !initial.abs().all_lt(1.0e10)
        || !c.emission.abs().all_lt(1.0e10)
        || !c.absorption.abs().all_lt(1.0e10)
        || !c.faraday.abs().all_lt(1.0e10)
    {
        return result;
    }
    let a = c.absorption;
    let scale = a.x.max(a.y.abs()).max(a.z.abs().max(a.w.abs()));
    // Normalize before squaring: subnormal opacities otherwise spuriously fail passivity.
    if a.x < 0.0 || (scale > 0.0 && a.x / scale < (a.yzw() / scale).length()) {
        return result;
    }
    let r = c.faraday;
    let k = mat4(
        vec4(a.x, a.y, a.z, a.w),
        vec4(a.y, a.x, -r.z, r.y),
        vec4(a.z, r.z, a.x, -r.x),
        vec4(a.w, -r.y, r.x, a.x),
    );
    let bound = a.x.abs() + (a.yzw().abs() + r.abs()).dot(vec3_splat(1.0));
    let mut h = ds;
    let mut squares = 0u32;
    while bound * h > 0.125 && squares < 16 {
        h *= 0.5;
        squares += 1;
    }
    if bound * h > 0.125 {
        return result;
    }
    let m = -h * k;
    let mut exponential = IDENTITY4;
    let mut term = IDENTITY4;
    let mut source = h * c.emission;
    let mut i = 1u32;
    // With ||hK|| <= 1/8, the ninth-order remainder is below 2.4e-14.
    while i <= 8 {
        term = (1.0 / i as f32) * (m * term);
        exponential += term;
        source += (h / (i + 1) as f32) * (term * c.emission);
        i += 1;
    }
    let mut s = 0u32;
    while s < squares {
        source = exponential * source + source;
        exponential = exponential * exponential;
        s += 1;
    }
    result.stokes = exponential * initial + source;
    result.transmission = exponential;
    result.valid = result.stokes.abs().all_lt(1.0e20);
    result
}

// -- Thermal coefficients -----------------------------------------------------

#[derive(Clone, Copy, Default)]
pub struct ThermalResult {
    pub coefficients: TransferCoefficients,
    pub valid: bool,
}

#[cuda_device::device]
unsafe fn thermal_bessel_ratios(t: f32, thermal_bessel: *const Vec2) -> Vec2 {
    let b0 = unsafe { *thermal_bessel };
    let b1 = unsafe { *thermal_bessel.add(1) };
    if t < b1.x {
        return vec2_splat(1.0);
    }
    if t < 0.002 {
        let mut sum = vec3_splat(1.0);
        let mut term = vec3_splat(1.0);
        let mut k = 1u32;
        while k <= 4 {
            let odd = (2 * k - 1) as f32;
            term = term * (vec3(0.0, 4.0, 16.0) - vec3_splat(odd * odd)) * (t / (8.0 * k as f32));
            sum += term;
            k += 1;
        }
        return sum.xy() / sum.z;
    }
    let index = clamp_f32((log(t) - b0.x) / b0.y, 0.0, 8192.0);
    let low = (index as u32).min(8191);
    let lo_v = unsafe { *thermal_bessel.add((low + 2) as usize) };
    let hi_v = unsafe { *thermal_bessel.add((low + 3) as usize) };
    lo_v.mix(hi_v, index - low as f32)
}

#[cuda_device::device]
unsafe fn thermal_coefficients(
    physical: Vec3,
    frequency: f32,
    mu: f32,
    thermal_bessel: *const Vec2,
) -> ThermalResult {
    let mut result = ThermalResult::default();
    let ne = physical.x;
    let t = physical.y;
    let b = physical.z;
    if !(ne >= 0.0
        && ne <= 1.0e12
        && t >= 0.001
        && t <= 1000.0
        && b >= 0.0
        && b <= 1.0e5
        && frequency >= 1.0e8
        && frequency <= 1.0e20
        && mu.abs() <= 1.0)
    {
        return result;
    }
    result.valid = true;
    if ne == 0.0 || b == 0.0 {
        return result;
    }
    let nu = frequency;
    let ratios = unsafe { thermal_bessel_ratios(t, thermal_bessel) };
    let s = sqrt((1.0 - mu * mu).max(0.0));
    let nuc = 2_799_250.5_f32 * b;
    let xfar = t * sqrt(1.414_213_5_f32 * s * 1.0e3 * nuc / nu);
    let faraday_scale = 7_736_369_600_000.0_f32 * ne / nu;
    let rho_v =
        2.0 * faraday_scale * (nuc / nu) * ratios.x * (1.0 - 0.11 * log(1.0 + 0.035 * xfar)) * mu;
    result.coefficients.faraday.z = rho_v;
    if s == 0.0 {
        return result;
    }
    let mut extra = 0.0;
    if xfar > 1.0 {
        extra = (0.011 * exp(-xfar / 47.2)
            - 0.011_767_707_f32 * 3.141_592_7_f32 * 1.0e4 * pow(xfar + 1.0e-16, -8.0 / 3.0))
            * (0.5 + 0.5 * tanh((log(xfar) - log(120.0)) / 0.1));
    }
    let jf = 2.011 * exp(-pow(xfar, 1.035) / 4.7)
        - cos(xfar / 2.0) * exp(-pow(xfar, 1.2) / 2.73)
        - 0.011 * exp(-xfar / 47.2)
        + extra;
    result.coefficients.faraday.x =
        faraday_scale * (nuc / nu) * (nuc / nu) * jf * (ratios.y + 6.0 * t) * s * s;
    let x = nu / (1.5 * nuc * s * t * t + 1.0);
    let root = pow(x, 1.0 / 3.0);
    let inv = 1.0 / root;
    let cutoff = exp(-1.8899 * root);
    let fi = 2.5651 * (1.0 + 1.92 * inv + 0.9977 * inv * inv);
    let fq = 2.5651 * (1.0 + 0.93193 * inv + 0.499873 * inv * inv);
    let fv = 1.81384 / x + 3.42319 * inv * inv + 0.0292545 / sqrt(x) + 2.03773 * inv;
    let g = 2.3e11 / nu;
    let scale = (2.034_396_2e-15 * ne * nu / (t * t)) * g * g * g;
    // Cap the dimensionless polarization before the exponential can underflow.
    let mut polarization = vec3(fq / fi, 0.0, (4.0 / (3.0 * t)) * (mu / s) * fv / fi);
    let fraction = polarization.length();
    if fraction > 0.99 {
        polarization *= 0.99 / fraction;
    }
    let intensity = scale * fi * cutoff;
    let j = vec4_f_v3(intensity, intensity * polarization);
    let planck_x = 8.093_3e-21 * nu / t;
    let mut denominator = exp(planck_x) - 1.0;
    if planck_x < 0.002 {
        denominator = planck_x / 24.0 * (24.0 + planck_x * (12.0 + planck_x * (4.0 + planck_x)));
    }
    let planck = 1.794_023_3e-13 / denominator;
    result.coefficients.emission = j;
    if planck > 0.0 {
        let alpha = intensity / planck;
        result.coefficients.absorption = vec4_f_v3(alpha, alpha * polarization);
    }
    result.valid = j.abs().all_lt(1.0e30)
        && result.coefficients.absorption.abs().all_lt(1.0e30)
        && result.coefficients.faraday.abs().all_lt(1.0e30);
    result
}

// -- Snapshot sampling --------------------------------------------------------

#[derive(Clone, Copy, Default)]
pub struct SnapshotSample {
    pub velocity: Vec4,
    pub magnetic: Vec4,
    pub physical: Vec4,
    pub native: Vec3,
    pub emitting: bool,
    pub valid: bool,
}

#[inline(always)]
fn snapshot_theta(x2: f32, hslope: f32) -> f32 {
    3.141592653589793 * x2 + 0.5 * (1.0 - hslope) * sin(6.283185307179586 * x2)
}

#[inline(always)]
fn snapshot_index(ijk: UVec3, grid: Vec3) -> usize {
    let sx = grid.x as u32 + 2;
    let sy = grid.y as u32 + 2;
    let sz = grid.z as u32 + 2;
    let _ = sx;
    ((ijk.x * sy + ijk.y) * sz + ijk.z) as usize
}

#[inline(always)]
fn snapshot_to_world_vector(v: Vec4, r: f32, th: f32, phi: f32, dth: f32, a: f32) -> Vec4 {
    let sc_th = sincos(th);
    let s = sc_th.x;
    let c = sc_th.y;
    let sc_phi = sincos(phi);
    let sp = sc_phi.x;
    let cp = sc_phi.y;
    let dr = vec3(r * cp * s, r * c, -r * sp * s);
    let dt = dth * vec3((r * cp - a * sp) * c, -r * s, -(r * sp + a * cp) * c);
    let dp = vec3(-(r * sp + a * cp) * s, 0.0, -(r * cp - a * sp) * s);
    vec4_f_v3(v.x, dr * v.y + dt * v.z + dp * v.w)
}

#[cuda_device::device]
unsafe fn sample_snapshot(
    pos: Vec3,
    header: &SnapshotHeader,
    primitives0: *const Vec4,
    primitives1: *const Vec4,
    physical_grid: *const Vec4,
) -> SnapshotSample {
    let mut result = SnapshotSample::default();
    if !pos.abs().all_le(2000.0) {
        return result;
    }
    if pos.x == 0.0 && pos.z == 0.0 {
        return result;
    }
    let a = header.geometry.x;
    let hslope = header.geometry.y;
    let q = pos.dot(pos) - a * a;
    let root = sqrt(q * q + 4.0 * a * a * pos.y * pos.y);
    let mut r2 = 0.5 * (q + root);
    if q < 0.0 {
        r2 = 2.0 * a * a * pos.y * pos.y / (root - q).max(1.0e-20);
    }
    if r2 <= 0.0 {
        return result;
    }
    let r = sqrt(r2);
    let th = atan2_arith(sqrt(pos.xz().dot(pos.xz()) / (r2 + a * a)), pos.y / r);
    let mut lo = 0.0;
    let mut hi = 1.0;
    let mut iter = 0u32;
    while iter < 25 {
        let mid = 0.5 * (lo + hi);
        if snapshot_theta(mid, hslope) < th {
            lo = mid;
        } else {
            hi = mid;
        }
        iter += 1;
    }
    let mut phi = atan2_arith(-r * pos.z - a * pos.x, r * pos.x - a * pos.z);
    if phi < 0.0 {
        phi += 6.283185307179586;
    }
    let x = vec3(log(r), 0.5 * (lo + hi), phi);
    let start = header.start.xyz();
    let grid = header.grid.xyz();
    let spacing = header.spacing.xyz();
    let stop = start + grid * spacing;
    if x.x < start.x || x.y < start.y || x.x >= stop.x || x.y >= stop.y {
        return result;
    }
    let raw_base = ((x - start) / spacing - vec3_splat(0.5)).floor();
    let base = raw_base.clamp(vec3_splat(-1.0), grid - vec3_splat(1.0));
    let d = ((x - (start + (base + vec3_splat(0.5)) * spacing)) / spacing)
        .clamp(vec3_splat(0.0), vec3_splat(1.0));
    let ijk = uvec3(
        (base.x + 1.0) as u32,
        (base.y + 1.0) as u32,
        (base.z + 1.0) as u32,
    );
    let mut p0 = vec4_splat(0.0);
    let mut p1 = vec4_splat(0.0);
    let mut physical = vec4_splat(0.0);
    let mut k = 0u32;
    while k < 2 {
        let mut j = 0u32;
        while j < 2 {
            let mut i = 0u32;
            while i < 2 {
                let wx = if i == 1 { d.x } else { 1.0 - d.x };
                let wy = if j == 1 { d.y } else { 1.0 - d.y };
                let wz = if k == 1 { d.z } else { 1.0 - d.z };
                let w = wx * wy * wz;
                let index = snapshot_index(ijk + uvec3(i, j, k), grid);
                p0 += w * unsafe { *primitives0.add(index) };
                p1 += w * unsafe { *primitives1.add(index) };
                physical += w * unsafe { *physical_grid.add(index) };
                i += 1;
            }
            j += 1;
        }
        k += 1;
    }
    let sc_th = sincos(th);
    let s2 = sc_th.x * sc_th.x;
    let rho2 = r2 + a * a * sc_th.y * sc_th.y;
    let f = 2.0 * r / rho2;
    let dth = 3.141592653589793 * (1.0 + (1.0 - hslope) * cos(6.283185307179586 * x.y));
    let g = mat4(
        vec4(-1.0 + f, f * r, 0.0, -a * f * s2),
        vec4(f * r, (1.0 + f) * r2, 0.0, -a * s2 * (1.0 + f) * r),
        vec4(0.0, 0.0, rho2 * dth * dth, 0.0),
        vec4(
            -a * f * s2,
            -a * s2 * (1.0 + f) * r,
            0.0,
            s2 * (rho2 + a * a * s2 * (1.0 + f)),
        ),
    );
    let v = vec4(0.0, p0.z, p0.w, p1.x);
    let fac = sqrt((1.0 + v.dot(g * v).abs()) / (1.0 + f));
    let u = vec4(fac * (1.0 + f), v.y - fac * f / r, v.z, v.w);
    let b0 = p1.yzw().dot((g * u).yzw());
    let b = vec4_f_v3(b0, (p1.yzw() + u.yzw() * b0) / u.x);
    result.velocity = snapshot_to_world_vector(u, r, th, phi, dth, a);
    result.magnetic = snapshot_to_world_vector(b, r, th, phi, dth, a);
    physical.x = if physical.w < header.physical.y {
        physical.x
    } else {
        0.0
    };
    result.physical = physical;
    result.native = x;
    result.emitting = r > header.geometry.z
        && r < header.geometry.w
        && th > header.physical.z
        && th < 3.141592653589793 - header.physical.z;
    result.valid = true;
    result
}

// -- Geodesic ray-tracer & Kerr-Schild metric ---------------------------------

#[inline(always)]
fn outer(a: Vec4, b: Vec4) -> Mat4 {
    mat4(a * b.x, a * b.y, a * b.z, a * b.w)
}

#[cuda_device::device]
fn kerr_radius(x: Vec3, a: Vec3) -> f32 {
    let q = x.dot(x) - a.dot(a);
    let ax = a.dot(x);
    let root = sqrt(q * q + 4.0 * ax * ax);
    let mut r2 = 0.5 * (q + root);
    if q < 0.0 {
        r2 = 2.0 * ax * ax / (root - q).max(1.0e-20);
    }
    sqrt(r2.max(1.0e-12))
}

#[cuda_device::device]
fn disk_radius(pos: Vec3, spin: f32, binary: bool) -> f32 {
    if binary {
        return pos.xz().length();
    }
    kerr_radius(
        vec3(pos.x, 0.0, pos.z),
        vec3(0.0, clamp_f32(spin, -0.999, 0.999), 0.0),
    )
}

/// The scene metric and its inverse. Derivatives are not stored: `geodesic_rhs`
/// contracts them per source (checklist P1.3), and `MetricJet` materializes them for
/// the diagnostics that need whole matrices.
#[derive(Clone, Copy, Default)]
pub struct Metric {
    pub g: Mat4,
    pub inv: Mat4,
    pub clearance: f32,
    pub valid: bool,
}

#[inline(always)]
fn flat_metric() -> Metric {
    Metric {
        g: ETA,
        inv: ETA,
        clearance: ESCAPE_R,
        valid: true,
    }
}

/// One Kerr–Schild source at offset `x`: g += 2h l l with covariant l = (1, ell).
#[derive(Clone, Copy, Default)]
struct KerrSource {
    a: Vec3,
    a2: f32,
    ax: f32,
    raw_r: f32,
    horizon: f32,
    r: f32,
    r2: f32,
    inv_den: f32,
    inv_r: f32,
    inv_r2: f32,
    inv_r2_a2: f32,
    h: f32,
    ell: Vec3,
}

#[inline(always)]
fn kerr_source(x: Vec3, mass: f32, spin: Vec3) -> KerrSource {
    let inv_spin_scale = 1.0 / (spin.length() / 0.999).max(1.0);
    let a = mass * spin * inv_spin_scale;
    let a2 = a.dot(a);
    let ax = a.dot(x);
    let raw_r = kerr_radius(x, a);
    let horizon = mass + sqrt((mass * mass - a2).max(0.0));
    let r = raw_r.max(0.8 * horizon);
    let r2 = r * r;
    let den = r2 * r2 + ax * ax;
    let inv_r = 1.0 / r;
    let inv_r2 = 1.0 / r2;
    let inv_den = 1.0 / den;
    let inv_r2_a2 = 1.0 / (r2 + a2);
    let h = mass * r * r2 * inv_den;
    let numerator = r * x - a.cross(x) + (ax * inv_r) * a;
    KerrSource {
        a, a2, ax, raw_r, horizon, r, r2, inv_den, inv_r, inv_r2, inv_r2_a2, h,
        ell: numerator * inv_r2_a2,
    }
}

/// Gradient of the source's Kerr radius (with r clamped as in `kerr_source`).
#[inline(always)]
fn kerr_radius_gradient(s: KerrSource, x: Vec3) -> Vec3 {
    let inv_dr = 1.0 / (2.0 * s.r2 - x.dot(x) + s.a2).max(1.0e-12);
    (s.r * x + (s.ax * s.inv_r) * s.a) * inv_dr
}

#[cuda_device::device]
fn add_kerr(base: Metric, x: Vec3, mass: f32, spin: Vec3) -> Metric {
    if mass <= 0.0 {
        return base;
    }
    add_kerr_source(base, kerr_source(x, mass, spin))
}

#[inline(always)]
fn add_kerr_source(base: Metric, s: KerrSource) -> Metric {
    let mut m = base;
    m.clearance = m.clearance.min(s.raw_r - s.horizon);
    let ell = vec4_f_v3(1.0, s.ell);
    m.g += 2.0 * s.h * outer(ell, ell);
    let raised = m.inv * ell;
    let divisor = 1.0 + 2.0 * s.h * ell.dot(raised);
    if divisor <= 1.0e-6 {
        m.valid = false;
        return m;
    }
    m.inv -= (2.0 * s.h / divisor) * outer(raised, raised);
    m.valid = m.valid && m.inv[0][0] < -1.0e-6;
    m
}

/// The source's metric derivatives d_x g, d_y g, d_z g as whole matrices.
#[inline(always)]
fn kerr_metric_derivatives(x: Vec3, mass: f32, spin: Vec3) -> [Mat4; 3] {
    if mass <= 0.0 {
        return [Mat4::default(); 3];
    }
    let s = kerr_source(x, mass, spin);
    let (a, r, h) = (s.a, s.r, s.h);
    let ell = vec4_f_v3(1.0, s.ell);
    let ll = outer(ell, ell);
    let dr = kerr_radius_gradient(s, x);
    let derivative = |ej: Vec3, dr_j: f32, a_j: f32| {
        let dh = h * (3.0 * dr_j * s.inv_r - (4.0 * r * s.r2 * dr_j + 2.0 * s.ax * a_j) * s.inv_den);
        let dn = dr_j * x + r * ej - a.cross(ej) + (a_j * s.inv_r - s.ax * dr_j * s.inv_r2) * a;
        let dl = vec4_f_v3(0.0, (dn - s.ell * 2.0 * r * dr_j) * s.inv_r2_a2);
        2.0 * dh * ll + 2.0 * h * (outer(dl, ell) + outer(ell, dl))
    };
    [
        derivative(vec3(1.0, 0.0, 0.0), dr.x, a.x),
        derivative(vec3(0.0, 1.0, 0.0), dr.y, a.y),
        derivative(vec3(0.0, 0.0, 1.0), dr.z, a.z),
    ]
}

#[cuda_device::device]
fn scene_metric(pos: Vec3, objects: &Objects) -> Metric {
    let mut m = flat_metric();
    let mut i = 0i32;
    while i < objects.num_objects {
        let idx = i as usize;
        let x = pos - objects.pos_radius[idx].xyz();
        m = add_kerr(m, x, objects.mass[idx].x.max(0.0), objects.spin[idx].xyz());
        i += 1;
    }
    m
}

/// A metric with its first derivatives as whole matrices, for diagnostics and the
/// reference `geodesic_rhs_matrix`.
#[derive(Clone, Copy, Default)]
pub struct MetricJet {
    pub m: Metric,
    pub dx: Mat4,
    pub dy: Mat4,
    pub dz: Mat4,
}

#[inline(always)]
fn add_kerr_jet(base: MetricJet, x: Vec3, mass: f32, spin: Vec3) -> MetricJet {
    let [dx, dy, dz] = kerr_metric_derivatives(x, mass, spin);
    MetricJet {
        m: add_kerr(base.m, x, mass, spin),
        dx: base.dx + dx,
        dy: base.dy + dy,
        dz: base.dz + dz,
    }
}

#[cuda_device::device]
fn plasma_metric(pos: Vec3, objects: &Objects) -> (Mat4, Mat4) {
    let m = scene_metric(pos, objects);
    (m.g, m.inv)
}

#[inline(always)]
fn spatial_metric(m: Metric) -> Mat3 {
    mat3(m.g[1].yzw(), m.g[2].yzw(), m.g[3].yzw())
}

#[cuda_device::device]
fn spatial_unit(v: Vec3, gamma: Mat3) -> Vec3 {
    let scale = v.x.abs().max(v.y.abs()).max(v.z.abs());
    if scale == 0.0 {
        return v;
    }
    let scaled = v / scale;
    scaled * inverse_sqrt(scaled.dot(gamma * scaled).max(1.0e-20))
}

#[derive(Clone, Copy, Default)]
pub struct Ray {
    pub pos: Vec3,
    pub p: Vec4,
    pub screen: Vec4,
}

#[cuda_device::device]
fn init_ray(pos: Vec3, dir: Vec3, m: Metric, cam: &Camera) -> Ray {
    let gamma = spatial_metric(m);
    let forward = spatial_unit(cam.forward, gamma);
    let right = spatial_unit(cam.right - forward * forward.dot(gamma * cam.right), gamma);
    let up = spatial_unit(
        cam.up - forward * forward.dot(gamma * cam.up) - right * right.dot(gamma * cam.up),
        gamma,
    );
    let n = spatial_unit(
        dir.dot(cam.forward) * forward + dir.dot(cam.right) * right + dir.dot(cam.up) * up,
        gamma,
    );
    let lapse = inverse_sqrt(-m.inv[0][0]);
    let shift = -m.inv[0].yzw() / m.inv[0][0];
    let k = vec4_f_v3(-1.0 / lapse, n + shift / lapse);
    let screen = spatial_unit(right - n * n.dot(gamma * right), gamma);
    Ray {
        pos,
        p: m.g * k,
        screen: vec4_f_v3(0.0, screen),
    }
}

#[derive(Clone, Copy, Default)]
pub struct Derivs {
    pub pos: Vec3,
    pub p: Vec4,
    pub screen: Vec4,
}

/// Reference right-hand side from whole derivative matrices. Its arithmetic is the
/// program `CudaGeodesic.geodesic_rhs_exact_inputs` bounds; `geodesic_rhs` must agree
/// with it (`bh_test_rhs_forms`).
#[inline(always)]
fn geodesic_rhs_matrix(ray: Ray, m: MetricJet) -> Derivs {
    let k = m.m.inv * ray.p;
    let dx_k = m.dx * k;
    let dy_k = m.dy * k;
    let dz_k = m.dz * k;
    let dx_f = m.dx * ray.screen;
    let dy_f = m.dy * ray.screen;
    let dz_f = m.dz * ray.screen;
    let contracted = vec4(
        0.0,
        k.dot(dx_f),
        k.dot(dy_f),
        k.dot(dz_f),
    );
    Derivs {
        pos: k.yzw(),
        p: 0.5 * vec4(0.0, k.dot(dx_k), k.dot(dy_k), k.dot(dz_k)),
        screen: -0.5
            * (m.m.inv
                * ((k.y * dx_f + k.z * dy_f + k.w * dz_f)
                    + (ray.screen.y * dx_k + ray.screen.z * dy_k + ray.screen.w * dz_k)
                    - contracted)),
    }
}

/// Geodesic and screen-transport right-hand side (checklist P1.3). Each source adds
/// d_i g = 2 d_i h l l + 2h (d_i l l + l d_i l) with l = (1, ell); only the contractions
/// with k = g^-1 p and the screen vector f are formed, never the matrices. The sum over
/// sources is the derivative of the superposed metric, and the inverse stays generic.
#[cuda_device::device]
fn geodesic_rhs(ray: Ray, m: Metric, objects: &Objects) -> Derivs {
    let k = m.inv * ray.p;
    // k . d_i g . k, and sum_i (k^i d_i g f + f^i d_i g k) - (0, k . d_i g . f).
    let mut force = vec3_splat(0.0);
    let mut transport = vec4_splat(0.0);
    let mut i = 0i32;
    while i < objects.num_objects {
        let idx = i as usize;
        let mass = objects.mass[idx].x.max(0.0);
        if mass > 0.0 {
            let x = ray.pos - objects.pos_radius[idx].xyz();
            let s = kerr_source(x, mass, objects.spin[idx].xyz());
            source_terms(s, x, k, ray.screen, &mut force, &mut transport);
        }
        i += 1;
    }
    rhs_from_terms(k, m, force, transport)
}

#[inline(always)]
fn rhs_from_terms(k: Vec4, m: Metric, force: Vec3, transport: Vec4) -> Derivs {
    Derivs {
        pos: k.yzw(),
        p: 0.5 * vec4_f_v3(0.0, force),
        screen: -0.5 * (m.inv * transport),
    }
}

/// The gradient of the source's h.
#[inline(always)]
fn kerr_h_gradient(s: KerrSource, dr: Vec3) -> Vec3 {
    s.h * (3.0 * s.inv_r * dr - (4.0 * s.r * s.r2 * dr + 2.0 * s.ax * s.a) * s.inv_den)
}

/// The gradient of ell . v at fixed v.
#[inline(always)]
fn ell_gradient(s: KerrSource, x: Vec3, dr: Vec3, v: Vec3) -> Vec3 {
    let av = s.a.dot(v);
    let grad_n = (x.dot(v) - s.ax * av * s.inv_r2) * dr + s.r * v - v.cross(s.a)
        + (av * s.inv_r) * s.a;
    (grad_n - (2.0 * s.r * s.ell.dot(v)) * dr) * s.inv_r2_a2
}

/// `source_terms`' force alone, for paths without screen transport.
#[inline(always)]
fn source_force(s: KerrSource, x: Vec3, k: Vec4) -> Vec3 {
    let ks = k.yzw();
    let dr = kerr_radius_gradient(s, x);
    let dh = kerr_h_gradient(s, dr);
    let u = k.x + s.ell.dot(ks);
    let gk = ell_gradient(s, x, dr, ks);
    2.0 * u * u * dh + 2.0 * (2.0 * s.h) * u * gk
}

/// One source's share of `geodesic_rhs`'s contractions.
#[inline(always)]
fn source_terms(s: KerrSource, x: Vec3, k: Vec4, f: Vec4, force: &mut Vec3, transport: &mut Vec4) {
    let (ks, fs) = (k.yzw(), f.yzw());
    let dr = kerr_radius_gradient(s, x);
    let dh = kerr_h_gradient(s, dr);
    // sum_j v_j d_j ell, with n = r x - a × x + (a.x / r) a = (r² + a²) ell.
    let along = |v: Vec3| {
        let dv_r = dr.dot(v);
        let dn = dv_r * x + s.r * v - s.a.cross(v)
            + (s.a.dot(v) * s.inv_r - s.ax * dv_r * s.inv_r2) * s.a;
        (dn - s.ell * (2.0 * s.r * dv_r)) * s.inv_r2_a2
    };
    let gradient = |v: Vec3| ell_gradient(s, x, dr, v);
    let u = k.x + s.ell.dot(ks);
    let w = f.x + s.ell.dot(fs);
    let (dk_l, df_l) = (along(ks), along(fs));
    let (gk, gf) = (gradient(ks), gradient(fs));
    let h2 = 2.0 * s.h;
    *force += 2.0 * u * u * dh + 2.0 * h2 * u * gk;
    let on_l = 2.0 * (w * dh.dot(ks) + u * dh.dot(fs) + s.h * (fs.dot(dk_l) + ks.dot(df_l)));
    let spatial = on_l * s.ell + h2 * (w * dk_l + u * df_l)
        - (2.0 * u * w * dh + h2 * (w * gk + u * gf));
    *transport += vec4_f_v3(on_l, spatial);
}

#[inline(always)]
fn rk_state(ray: Ray, d: Derivs, h: f32) -> Ray {
    Ray {
        pos: ray.pos + h * d.pos,
        p: ray.p + h * d.p,
        screen: ray.screen + h * d.screen,
    }
}

#[derive(Clone, Copy, Default)]
pub struct RayStep {
    pub ray: Ray,
    pub valid: bool,
}

#[inline(always)]
fn ray_valid(ray: Ray, m: Metric) -> bool {
    m.valid
        && m.clearance > 0.0
        && ray.pos.abs().all_lt(1.0e8)
        && ray.p.abs().all_lt(1.0e8)
        && ray.screen.abs().all_lt(1.0e8)
}

#[cuda_device::device]
fn ray_endpoint_valid(ray: Ray, objects: &Objects) -> bool {
    ray_valid(ray, scene_metric(ray.pos, objects))
}

#[inline(always)]
fn ray_rhs(ray: Ray, m: Metric, gauged: bool, objects: &Objects) -> Derivs {
    gauge(geodesic_rhs(ray, m, objects), m.inv * ray.p, gauged)
}

#[inline(always)]
fn gauge(d: Derivs, k: Vec4, gauged: bool) -> Derivs {
    let mut result = d;
    if gauged {
        if k.x.abs() > 1.0e-20 {
            result.screen -= k * (result.screen.x / k.x);
            result.screen.x = 0.0;
        }
    }
    result
}

#[cuda_device::device]
fn rk4_stages(ray: Ray, h: f32, k1: Derivs, gauged: bool, objects: &Objects) -> Option<Ray> {
    let r2 = rk_state(ray, k1, 0.5 * h);
    let m2 = scene_metric(r2.pos, objects);
    if !ray_valid(r2, m2) {
        return None;
    }
    let k2 = ray_rhs(r2, m2, gauged, objects);
    let r3 = rk_state(ray, k2, 0.5 * h);
    let m3 = scene_metric(r3.pos, objects);
    if !ray_valid(r3, m3) {
        return None;
    }
    let k3 = ray_rhs(r3, m3, gauged, objects);
    let r4 = rk_state(ray, k3, h);
    let m4 = scene_metric(r4.pos, objects);
    if !ray_valid(r4, m4) {
        return None;
    }
    let k4 = ray_rhs(r4, m4, gauged, objects);
    Some(rk_state(
        ray,
        Derivs {
            pos: k1.pos + 2.0 * k2.pos + 2.0 * k3.pos + k4.pos,
            p: k1.p + 2.0 * k2.p + 2.0 * k3.p + k4.p,
            screen: k1.screen + 2.0 * k2.screen + 2.0 * k3.screen + k4.screen,
        },
        h / 6.0,
    ))
}

#[inline(always)]
fn step_ray(ray: Ray, h: f32, m: Metric, objects: &Objects) -> RayStep {
    if ray_valid(ray, m)
        && let Some(next) = rk4_stages(ray, h, ray_rhs(ray, m, false, objects), false, objects)
    {
        return RayStep {
            ray: next,
            valid: ray_endpoint_valid(next, objects),
        };
    }
    RayStep { ray, valid: false }
}

#[inline(always)]
fn relative_difference(a: Vec4, b: Vec4) -> f32 {
    let d = (a - b).abs() / vec4_splat(1.0).max(a.abs().max(b.abs()));
    d.x.max(d.y).max(d.z.max(d.w))
}

#[derive(Clone, Copy, Default)]
pub struct AdaptiveStep {
    pub ray: Ray,
    pub h: f32,
    pub error: f32,
    pub accepted: bool,
    /// d/dλ of the state at the start and end of an accepted Dormand–Prince step, for
    /// Hermite dense output; zero from the other controllers.
    pub rates: [Derivs; 2],
}

#[cuda_device::device]
fn advance_ray_gauge(
    ray: Ray,
    requested_h: f32,
    m: &mut Metric,
    gauged: bool,
    objects: &Objects,
) -> AdaptiveStep {
    advance_ray_counting::<false>(ray, requested_h, m, gauged, objects, &mut 0)
}

#[inline(always)]
fn advance_ray_counting<const DIAGNOSTICS: bool>(
    ray: Ray,
    requested_h: f32,
    m: &mut Metric,
    gauged: bool,
    objects: &Objects,
    rejected: &mut u32,
) -> AdaptiveStep {
    if !(requested_h > 0.0 && requested_h < 1.0e8 && ray_valid(ray, *m)) {
        return AdaptiveStep {
            ray,
            h: 0.0,
            error: 1.0e30,
            accepted: false,
            rates: [Derivs::default(); 2],
        };
    }
    // The coarse step, the first half step and every retry start from the same state.
    let initial_rhs = ray_rhs(ray, *m, gauged, objects);
    let mut next_h = requested_h;
    for retry in 0..12 {
        let h = next_h;
        next_h = 0.5 * h;
        let Some(coarse) = rk4_stages(ray, h, initial_rhs, gauged, objects) else {
            continue;
        };
        if !ray_endpoint_valid(coarse, objects) {
            continue;
        }
        let Some(half) = rk4_stages(ray, next_h, initial_rhs, gauged, objects) else {
            continue;
        };
        let half_metric = scene_metric(half.pos, objects);
        if !ray_valid(half, half_metric) {
            continue;
        }
        let half_rhs = ray_rhs(half, half_metric, gauged, objects);
        let Some(fine) = rk4_stages(half, next_h, half_rhs, gauged, objects) else {
            continue;
        };
        let metric = scene_metric(fine.pos, objects);
        if !ray_valid(fine, metric) {
            continue;
        }
        let error = relative_difference(vec4_v3_f(coarse.pos, 0.0), vec4_v3_f(fine.pos, 0.0))
            .max(
                relative_difference(coarse.p, fine.p)
                    .max(relative_difference(coarse.screen, fine.screen)),
            )
            / 15.0;
        let null_error = fine.p.dot(metric.inv * fine.p).abs() / fine.p.dot(fine.p).max(1.0e-10);
        if error <= STEP_TOLERANCE
            && null_error < 2.0e-4
            && (fine.pos.x != ray.pos.x || fine.pos.y != ray.pos.y || fine.pos.z != ray.pos.z)
        {
            if DIAGNOSTICS {
                *rejected += retry;
            }
            *m = metric;
            return AdaptiveStep {
                ray: fine,
                h,
                error,
                accepted: true,
                rates: [Derivs::default(); 2],
            };
        }
    }
    if DIAGNOSTICS {
        *rejected += 12;
    }
    AdaptiveStep {
        ray,
        h: 0.0,
        error: 1.0e30,
        accepted: false,
        rates: [Derivs::default(); 2],
    }
}

#[inline(always)]
fn add_derivs(a: Derivs, w: f32, k: Derivs) -> Derivs {
    Derivs {
        pos: a.pos + w * k.pos,
        p: a.p + w * k.p,
        screen: a.screen + w * k.screen,
    }
}

#[inline(always)]
fn scale_derivs(w: f32, k: Derivs) -> Derivs {
    Derivs {
        pos: w * k.pos,
        p: w * k.p,
        screen: w * k.screen,
    }
}

/// The metric at `r` and, when the ray is valid there, its right-hand side. With one or
/// two holes each source is computed once for both (checklist P1.3); the metric is
/// built in `scene_metric`'s order, so it is the same bits.
#[cuda_device::device]
fn metric_and_rhs(r: Ray, gauged: bool, objects: &Objects) -> (Metric, Option<Derivs>) {
    if objects.num_objects <= 2 {
        let slot = |i: usize| {
            let live = objects.num_objects > i as i32 && objects.mass[i].x > 0.0;
            let x = r.pos - objects.pos_radius[i].xyz();
            let s = if live {
                kerr_source(x, objects.mass[i].x, objects.spin[i].xyz())
            } else {
                KerrSource::default()
            };
            (live, x, s)
        };
        let (live0, x0, s0) = slot(0);
        let (live1, x1, s1) = slot(1);
        let mut m = flat_metric();
        if live0 {
            m = add_kerr_source(m, s0);
        }
        if live1 {
            m = add_kerr_source(m, s1);
        }
        if !ray_valid(r, m) {
            return (m, None);
        }
        let k = m.inv * r.p;
        let (mut force, mut transport) = (vec3_splat(0.0), vec4_splat(0.0));
        if live0 {
            source_terms(s0, x0, k, r.screen, &mut force, &mut transport);
        }
        if live1 {
            source_terms(s1, x1, k, r.screen, &mut force, &mut transport);
        }
        return (m, Some(gauge(rhs_from_terms(k, m, force, transport), k, gauged)));
    }
    let m = scene_metric(r.pos, objects);
    if !ray_valid(r, m) {
        return (m, None);
    }
    (m, Some(ray_rhs(r, m, gauged, objects)))
}

/// Render paths (checklist P1.2). `SINGLE`: exactly one source. `SINGLE_SCALAR`: one
/// source and thermal intensity alone, which never reads the screen vector, so it is
/// not transported and the step error omits it.
const GENERIC: u8 = 0;
const SINGLE: u8 = 1;
const SINGLE_SCALAR: u8 = 2;

/// `metric_and_rhs` for exactly one source: the operations of its two-slot path with
/// slot 1 empty, so the same bits, without slot 1's live state.
#[cuda_device::device]
fn metric_and_rhs_one(r: Ray, gauged: bool, objects: &Objects) -> (Metric, Option<Derivs>) {
    single_metric_and_rhs::<false>(r, gauged, objects)
}

/// `metric_and_rhs_one` without screen transport: the screen derivative is zero.
#[cuda_device::device]
fn metric_and_rhs_scalar(r: Ray, objects: &Objects) -> (Metric, Option<Derivs>) {
    single_metric_and_rhs::<true>(r, false, objects)
}

#[inline(always)]
fn single_metric_and_rhs<const SCALAR: bool>(r: Ray, gauged: bool, objects: &Objects) -> (Metric, Option<Derivs>) {
    let live = objects.mass[0].x > 0.0;
    let x = r.pos - objects.pos_radius[0].xyz();
    let s = if live {
        kerr_source(x, objects.mass[0].x, objects.spin[0].xyz())
    } else {
        KerrSource::default()
    };
    let mut m = flat_metric();
    if live {
        m = add_kerr_source(m, s);
    }
    if !ray_valid(r, m) {
        return (m, None);
    }
    let k = m.inv * r.p;
    if SCALAR {
        let force = if live { source_force(s, x, k) } else { vec3_splat(0.0) };
        return (m, Some(scalar_rhs(k, force)));
    }
    let (mut force, mut transport) = (vec3_splat(0.0), vec4_splat(0.0));
    if live {
        source_terms(s, x, k, r.screen, &mut force, &mut transport);
    }
    (m, Some(gauge(rhs_from_terms(k, m, force, transport), k, gauged)))
}

#[inline(always)]
fn scalar_rhs(k: Vec4, force: Vec3) -> Derivs {
    Derivs {
        pos: k.yzw(),
        p: 0.5 * vec4_f_v3(0.0, force),
        screen: vec4_splat(0.0),
    }
}

#[inline(always)]
fn stage_metric_and_rhs<const PATH: u8>(r: Ray, gauged: bool, objects: &Objects) -> (Metric, Option<Derivs>) {
    match PATH {
        SINGLE => metric_and_rhs_one(r, gauged, objects),
        SINGLE_SCALAR => metric_and_rhs_scalar(r, objects),
        _ => metric_and_rhs(r, gauged, objects),
    }
}

/// The right-hand side at a ray whose metric `m` is already known.
#[inline(always)]
fn first_stage<const PATH: u8>(ray: Ray, m: Metric, gauged: bool, objects: &Objects) -> Derivs {
    if PATH == SINGLE_SCALAR {
        let k = m.inv * ray.p;
        let mass = objects.mass[0].x.max(0.0);
        let force = if mass > 0.0 {
            let x = ray.pos - objects.pos_radius[0].xyz();
            source_force(kerr_source(x, mass, objects.spin[0].xyz()), x, k)
        } else {
            vec3_splat(0.0)
        };
        return scalar_rhs(k, force);
    }
    ray_rhs(ray, m, gauged, objects)
}

#[inline(always)]
fn dp_stage<const PATH: u8>(ray: Ray, d: Derivs, h: f32, gauged: bool, objects: &Objects) -> Option<Derivs> {
    stage_metric_and_rhs::<PATH>(rk_state(ray, d, h), gauged, objects).1
}

#[inline(always)]
fn relative_size(e: Vec4, y: Vec4) -> f32 {
    let d = e.abs() / vec4_splat(1.0).max(y.abs());
    d.x.max(d.y).max(d.z.max(d.w))
}

/// Dormand–Prince 5(4) tableau: stage rows, fifth-order weights over k1–k6 and error
/// weights (fifth minus fourth order) over k1–k7. `verification/BlackHole/DormandPrince.lean`
/// proves the order conditions; `tests/dormand_prince_tableau.rs` checks these literals
/// against it.
const DP_A: [[f32; 5]; 5] = [
    [1.0 / 5.0, 0.0, 0.0, 0.0, 0.0],
    [3.0 / 40.0, 9.0 / 40.0, 0.0, 0.0, 0.0],
    [44.0 / 45.0, -56.0 / 15.0, 32.0 / 9.0, 0.0, 0.0],
    [19372.0 / 6561.0, -25360.0 / 2187.0, 64448.0 / 6561.0, -212.0 / 729.0, 0.0],
    [9017.0 / 3168.0, -355.0 / 33.0, 46732.0 / 5247.0, 49.0 / 176.0, -5103.0 / 18656.0],
];
const DP_B: [f32; 6] = [35.0 / 384.0, 0.0, 500.0 / 1113.0, 125.0 / 192.0, -2187.0 / 6784.0, 11.0 / 84.0];
const DP_E: [f32; 7] = [
    71.0 / 57600.0, 0.0, -71.0 / 16695.0, 71.0 / 1920.0, -17253.0 / 339200.0, 22.0 / 525.0, -1.0 / 40.0,
];

/// The renderer's controller (checklist P1.1/P1.1b): embedded Dormand–Prince 5(4), advancing the fifth-order
/// solution. Six metric evaluations per first-try step against eleven for step doubling.
/// No FSAL: callers rewrite `screen` between steps, and the endpoint metric is reused anyway.
#[inline(always)]
fn advance_ray_dp45<const DIAGNOSTICS: bool, const PATH: u8>(
    ray: Ray,
    requested_h: f32,
    m: &mut Metric,
    gauged: bool,
    objects: &Objects,
    rejected: &mut u32,
) -> AdaptiveStep {
    if !(requested_h > 0.0 && requested_h < 1.0e8 && ray_valid(ray, *m)) {
        return AdaptiveStep {
            ray,
            h: 0.0,
            error: 1.0e30,
            accepted: false,
            rates: [Derivs::default(); 2],
        };
    }
    let k1 = first_stage::<PATH>(ray, *m, gauged, objects);
    let mut next_h = requested_h;
    for retry in 0..12 {
        let h = next_h;
        next_h = 0.5 * h;
        let Some(k2) = dp_stage::<PATH>(ray, scale_derivs(DP_A[0][0], k1), h, gauged, objects) else {
            continue;
        };
        let d = add_derivs(scale_derivs(DP_A[1][0], k1), DP_A[1][1], k2);
        let Some(k3) = dp_stage::<PATH>(ray, d, h, gauged, objects) else {
            continue;
        };
        let d = add_derivs(
            add_derivs(scale_derivs(DP_A[2][0], k1), DP_A[2][1], k2),
            DP_A[2][2],
            k3,
        );
        let Some(k4) = dp_stage::<PATH>(ray, d, h, gauged, objects) else {
            continue;
        };
        let d = add_derivs(
            add_derivs(
                add_derivs(scale_derivs(DP_A[3][0], k1), DP_A[3][1], k2),
                DP_A[3][2],
                k3,
            ),
            DP_A[3][3],
            k4,
        );
        let Some(k5) = dp_stage::<PATH>(ray, d, h, gauged, objects) else {
            continue;
        };
        let d = add_derivs(
            add_derivs(
                add_derivs(
                    add_derivs(scale_derivs(DP_A[4][0], k1), DP_A[4][1], k2),
                    DP_A[4][2],
                    k3,
                ),
                DP_A[4][3],
                k4,
            ),
            DP_A[4][4],
            k5,
        );
        let Some(k6) = dp_stage::<PATH>(ray, d, h, gauged, objects) else {
            continue;
        };
        let d = add_derivs(
            add_derivs(
                add_derivs(
                    add_derivs(scale_derivs(DP_B[0], k1), DP_B[2], k3),
                    DP_B[3],
                    k4,
                ),
                DP_B[4],
                k5,
            ),
            DP_B[5],
            k6,
        );
        let next = rk_state(ray, d, h);
        let (metric, k7) = stage_metric_and_rhs::<PATH>(next, gauged, objects);
        let Some(k7) = k7 else {
            continue;
        };
        // Difference between the fifth- and fourth-order solutions, formed directly
        // from the stages so it is not lost to binary32 rounding of the two states.
        let e = scale_derivs(
            h,
            add_derivs(
                add_derivs(
                    add_derivs(
                        add_derivs(
                            add_derivs(scale_derivs(DP_E[0], k1), DP_E[2], k3),
                            DP_E[3],
                            k4,
                        ),
                        DP_E[4],
                        k5,
                    ),
                    DP_E[5],
                    k6,
                ),
                DP_E[6],
                k7,
            ),
        );
        let error = relative_size(vec4_v3_f(e.pos, 0.0), vec4_v3_f(next.pos, 0.0))
            .max(relative_size(e.p, next.p).max(relative_size(e.screen, next.screen)));
        let null_error = next.p.dot(metric.inv * next.p).abs() / next.p.dot(next.p).max(1.0e-10);
        if error <= STEP_TOLERANCE
            && null_error < 2.0e-4
            && (next.pos.x != ray.pos.x || next.pos.y != ray.pos.y || next.pos.z != ray.pos.z)
        {
            if DIAGNOSTICS {
                *rejected += retry;
            }
            *m = metric;
            return AdaptiveStep {
                ray: next,
                h,
                error,
                accepted: true,
                rates: [k1, k7],
            };
        }
    }
    if DIAGNOSTICS {
        *rejected += 12;
    }
    AdaptiveStep {
        ray,
        h: 0.0,
        error: 1.0e30,
        accepted: false,
        rates: [Derivs::default(); 2],
    }
}

/// Angle between two positions as seen from the origin.
#[inline(always)]
fn swept_angle(a: Vec3, b: Vec3) -> f32 {
    atan2_arith(a.cross(b).length(), a.dot(b))
}

/// Unresolved band (checklist P1.6): a ray that has swept more than this angle around
/// the origin ends unresolved rather than captured or escaped. Near the photon sphere
/// the winding grows like -ln|margin|, where margin = (E² - V_max)/E², so the band is
/// about |margin| < 6e-5 for escapes and 1.5e-5 for captures, whatever the controller.
/// In the Schwarzschild classification test, every wrong answer from either controller
/// at step factors 0.11-0.13 had swept at least 16.1 rad: e^2.1 ≈ 8 times inside the band.
/// shortcut: winding is measured about the origin, the hole in the single-source scenes
/// it was validated on; binaries get no calibrated band.
const UNRESOLVED_WINDING: f32 = 14.0;

#[inline(always)]
fn advance_ray(ray: Ray, requested_h: f32, mut m: Metric, objects: &Objects) -> AdaptiveStep {
    advance_ray_gauge(ray, requested_h, &mut m, false, objects)
}

#[cuda_device::device]
fn screen_frame(ray: Ray, m: Metric) -> Mat3 {
    screen_frame_at(ray, m.g, m.inv)
}

#[inline(always)]
fn screen_frame_at(ray: Ray, g: Mat4, inv: Mat4) -> Mat3 {
    let k = inv * ray.p;
    let shift = -inv[0].yzw() * (1.0 / inv[0][0]);
    let gamma = mat3(g[1].yzw(), g[2].yzw(), g[3].yzw());
    let n = spatial_unit(k.yzw() + shift * k.x, gamma);
    let f = ray.screen.yzw() - k.yzw() * (ray.screen.x / k.x);
    let e1 = spatial_unit(f - n * n.dot(gamma * f), gamma);
    let e2 = spatial_unit((gamma * n).cross(gamma * e1), gamma);
    mat3(e1, e2, n)
}

const PIO2_HI: f32 = 1.5707963705062866;
const PIO2_LO: f32 = -4.371138828673793e-8;
const TWO_OVER_PI: f32 = 0.6366197466850281;

#[cuda_device::device]
fn sincos(x: f32) -> Vec2 {
    let k = round_even(cuda_device::float::mul_rn_f32(x, TWO_OVER_PI));
    let x_hi = cuda_device::float::add_rn_f32(x, -cuda_device::float::mul_rn_f32(k, PIO2_HI));
    let r = clamp_f32(
        cuda_device::float::add_rn_f32(x_hi, -cuda_device::float::mul_rn_f32(k, PIO2_LO)),
        -1.0,
        1.0,
    );
    let r2 = r * r;
    let s = r
        * (1.0
            + r2 * (-1.0 / 6.0
                + r2 * (1.0 / 120.0
                    + r2 * (-1.0 / 5040.0
                        + r2 * (1.0 / 362880.0
                            + r2 * (-1.0 / 39916800.0 + r2 * (1.0 / 6227020800.0)))))));
    let c = 1.0
        + r2 * (-0.5
            + r2 * (1.0 / 24.0
                + r2 * (-1.0 / 720.0
                    + r2 * (1.0 / 40320.0
                        + r2 * (-1.0 / 3628800.0
                            + r2 * (1.0 / 479001600.0 + r2 * (-1.0 / 87178291200.0)))))));
    let q = (k as i32) & 3;
    if q == 0 {
        return vec2(s, c);
    }
    if q == 1 {
        return vec2(c, -s);
    }
    if q == 2 {
        return vec2(-s, -c);
    }
    vec2(-c, s)
}

#[cuda_device::device]
fn faraday_rotation(rho: Vec3, ds: f32) -> Mat3 {
    let w = rho.length();
    let axis = rho * (1.0 / w.max(1.0e-20));
    let angle = w * ds;
    let sc = sincos(angle);
    let c = sc.y;
    let s = sc.x;
    let identity = mat3(
        vec3(1.0, 0.0, 0.0),
        vec3(0.0, 1.0, 0.0),
        vec3(0.0, 0.0, 1.0),
    );
    let cross_matrix = mat3(
        vec3(0.0, axis.z, -axis.y),
        vec3(-axis.z, 0.0, axis.x),
        vec3(axis.y, -axis.x, 0.0),
    );
    let aa = mat3(axis * axis.x, axis * axis.y, axis * axis.z);
    c * identity + s * cross_matrix + (1.0 - c) * aa
}

#[cuda_device::device]
fn transfer_phi(z: Vec2) -> Vec2 {
    if z.dot(z) < 0.25 {
        let c = [
            1.0_f32,
            0.5,
            1.0 / 6.0,
            1.0 / 24.0,
            1.0 / 120.0,
            1.0 / 720.0,
            1.0 / 5040.0,
            1.0 / 40320.0,
            1.0 / 362880.0,
            1.0 / 3628800.0,
            1.0 / 39916800.0,
        ];
        let mut acc = vec2(c[10], 0.0);
        let mut k = 9i32;
        while k >= 0 {
            acc = vec2(
                c[k as usize] - (z.x * acc.x - z.y * acc.y),
                -(z.x * acc.y + z.y * acc.x),
            );
            k -= 1;
        }
        return acc;
    }
    let e = exp(-z.x);
    let sc = sincos(z.y);
    let num = vec2(1.0 - e * sc.y, e * sc.x);
    vec2(num.x * z.x + num.y * z.y, num.y * z.x - num.x * z.y) / z.dot(z)
}

#[inline(always)]
fn absorption_integral(alpha: f32, ds: f32) -> f32 {
    ds * transfer_phi(vec2(alpha * ds, 0.0)).x
}

#[cuda_device::device]
fn polarized_cell(j: Vec4, alpha: f32, rho: Vec3, ds: f32) -> Vec4 {
    let integral = absorption_integral(alpha, ds);
    let w = rho.length();
    // Skipping the in-cell turn costs w ds / 2 of the polarized emission.
    if w * ds < 1.0e-7 {
        return j * integral;
    }
    let axis = rho * (1.0 / w);
    let parallel = axis * axis.dot(j.yzw());
    let perpendicular = j.yzw() - parallel;
    let rotated = ds * transfer_phi(vec2(alpha * ds, -w * ds));
    let ic = rotated.x;
    let is = rotated.y;
    vec4_f_v3(
        j.x * integral,
        integral * parallel + ic * perpendicular + is * axis.cross(perpendicular),
    )
}

/// Decoupled transfer (checklist P1.9): most constant cells one geodesic step's plasma
/// is split into. Longer steps through the slab left the thin-disk Stokes error twice
/// the coupled scheme's at 32 cells; at 8 it matches, for 3% more steps.
const MAX_TRANSFER_CELLS: u32 = 8;

/// Longest decoupled transfer cell as a fraction of the radius, for emissivity and
/// Doppler variation along the orbit: the hot flow's quarter scale height (0.125 r) left
/// a p99 relative intensity error of 2.4e-4; 0.05 r brings it to 8.9e-5.
const ORBIT_CELL: f32 = 0.05;

/// Cubic Hermite dense output at fraction `u` of an accepted step of length `h`.
#[inline(always)]
fn hermite_ray(a: Ray, b: Ray, rates: [Derivs; 2], h: f32, u: f32) -> Ray {
    let u2 = u * u;
    let u3 = u2 * u;
    let (w0, w1) = (2.0 * u3 - 3.0 * u2 + 1.0, h * (u3 - 2.0 * u2 + u));
    let (w2, w3) = (3.0 * u2 - 2.0 * u3, h * (u3 - u2));
    let [r0, r1] = rates;
    Ray {
        pos: w0 * a.pos + w1 * r0.pos + w2 * b.pos + w3 * r1.pos,
        p: w0 * a.p + w1 * r0.p + w2 * b.p + w3 * r1.p,
        screen: w0 * a.screen + w1 * r0.screen + w2 * b.screen + w3 * r1.screen,
    }
}

/// Adds one constant-coefficient plasma cell of length `ds` behind the accumulated
/// foreground (front to back along the backward ray).
#[inline(always)]
fn composite_plasma(
    plasma: &Plasma,
    ds: f32,
    polarized: bool,
    rgb: &mut Vec3,
    stokes: &mut Vec4,
    transmission: &mut f32,
    foreground: &mut Mat3,
) {
    if polarized {
        let cell = polarized_cell(plasma.j, plasma.alpha, plasma.rho, ds);
        *stokes += *transmission * vec4_f_v3(cell.x, *foreground * cell.yzw());
        *foreground = *foreground * faraday_rotation(plasma.rho, ds);
    }
    *rgb += *transmission * plasma.rgb * absorption_integral(plasma.alpha, ds);
    *transmission *= exp(-plasma.alpha * ds);
}

#[derive(Clone, Copy, Default)]
pub struct ObjectHit {
    pub hit: bool,
    pub color: Vec4,
    pub center: Vec3,
    pub radius: f32,
}

#[inline(always)]
fn intersect_objects_segment(start: Vec3, end: Vec3, objects: &Objects) -> ObjectHit {
    let mut result = ObjectHit::default();
    let segment = end - start;
    let segment_len2 = segment.dot(segment).max(1.0e-12);
    let mut i = 0i32;
    while i < objects.num_objects {
        let idx = i as usize;
        let center = objects.pos_radius[idx].xyz();
        let radius = objects.pos_radius[idx].w;
        let t = clamp_f32((center - start).dot(segment) / segment_len2, 0.0, 1.0);
        let closest = start + segment * t;
        let offset = closest - center;
        if radius >= 0.0 && offset.dot(offset) <= radius * radius {
            result.hit = true;
            result.color = objects.color[idx];
            result.center = center;
            result.radius = radius;
            return result;
        }
        i += 1;
    }
    result
}

/// Time slices of the swarm BVH, in camera-relative coordinate time. Slice k
/// covers [-(k+1) W, -k W]; its boxes also cover SWARM_STEP_SPAN / 2 on each side,
/// so any step no longer than SWARM_STEP_SPAN whose midpoint lies in the slice fits.
/// Must match `SLICE_WIDTH` and `STEP_SPAN` in `src/swarm.rs`.
const SWARM_SLICE_WIDTH: f32 = 8.0;
const SWARM_STEP_SPAN: f32 = 12.0;
/// Slices the host builds; must match `SLICES` in `src/swarm.rs`.
const SWARM_SLICES: f32 = 40.0;

/// Segment `start → end`, traversed between camera-relative times `t0 → t1`.
#[derive(Clone, Copy)]
struct SwarmQuery {
    start: Vec3,
    segment: Vec3,
    t0: f32,
    t1: f32,
    near_r: f32,
    far_r: f32,
}

#[inline(always)]
fn swarm_query(start: Vec3, end: Vec3, t0: f32, t1: f32) -> SwarmQuery {
    let segment = end - start;
    let segment_len2 = segment.dot(segment).max(1.0e-12);
    let nearest = clamp_f32(-start.dot(segment) / segment_len2, 0.0, 1.0);
    SwarmQuery {
        start,
        segment,
        t0,
        t1,
        near_r: (start + nearest * segment).length(),
        far_r: start.length().max(end.length()),
    }
}

/// Tests one body. Its motion over the step is linearized and its radius padded by
/// the arc's sagitta, so the test is conservative. Keeps the earliest hit in
/// `best` (segment parameter) and its lit colour in `result`.
#[cuda_device::device]
fn swarm_body_hit(q: SwarmQuery, body: SwarmBody, best: &mut f32, result: &mut Vec4) {
    let orbit_r = body.axis_a.w;
    let omega = body.orbit.y;
    let turn = omega * (q.t1 - q.t0);
    let radius = body.axis_b.w + 0.125 * orbit_r * turn * turn;
    // Each orbit lies on a sphere of radius orbit_r and in a fixed plane; skip
    // bodies the segment cannot reach before evaluating their positions.
    if orbit_r + radius < q.near_r || orbit_r - radius > q.far_r {
        return;
    }
    let end = q.start + q.segment;
    let normal = body.axis_a.xyz().cross(body.axis_b.xyz());
    let h0 = normal.dot(q.start);
    let h1 = normal.dot(end);
    if (h0 > radius && h1 > radius) || (h0 < -radius && h1 < -radius) {
        return;
    }
    let s0 = sincos(body.orbit.x + omega * q.t0);
    let s1 = sincos(body.orbit.x + omega * q.t1);
    let c0 = orbit_r * (s0.y * body.axis_a.xyz() + s0.x * body.axis_b.xyz());
    let c1 = orbit_r * (s1.y * body.axis_a.xyz() + s1.x * body.axis_b.xyz());
    // Relative motion: |rel + s d| = radius for s in [0, 1].
    let rel = q.start - c0;
    let d = q.segment - (c1 - c0);
    let dd = d.dot(d).max(1.0e-12);
    let half_b = rel.dot(d);
    let disc = half_b * half_b - dd * (rel.dot(rel) - radius * radius);
    if disc < 0.0 {
        return;
    }
    let root = sqrt(disc);
    let entry = (-half_b - root) / dd;
    let exit = (-half_b + root) / dd;
    let s = entry.max(0.0);
    if exit >= 0.0 && entry <= 1.0 && s < *best {
        *best = s;
        let center = c0 + s * (c1 - c0);
        let normal = (rel + s * d).normalize();
        // Lit by the inner disk: the hemisphere facing the hole is bright.
        let facing = normal.dot(-center.normalize()).max(0.0);
        let light = (10.0 / orbit_r) * (10.0 / orbit_r);
        *result = vec4_v3_f(
            body.orbit.z * vec3(0.62, 0.52, 0.44) * (0.03 + 4.0 * light * facing),
            1.0,
        );
    }
}

/// Brute force over every body. Returns the lit colour of the earliest hit in xyz
/// with w = 1, or w = 0 for a miss.
#[cuda_device::device]
fn swarm_segment_hit(
    start: Vec3,
    end: Vec3,
    t0: f32,
    t1: f32,
    swarm: *const SwarmBody,
    count: u32,
) -> Vec4 {
    let q = swarm_query(start, end, t0, t1);
    let mut best = 2.0_f32;
    let mut result = vec4_splat(0.0);
    let mut i = 0u32;
    while i < count {
        swarm_body_hit(q, unsafe { *swarm.add(i as usize) }, &mut best, &mut result);
        i += 1;
    }
    result
}

/// Whether the step stays outside the shell that holds every body over its duration
/// dt: radii [inner - pad, outer + pad] with pad = spread dt^2, the largest arc
/// sagitta `swarm_body_hit` adds. See `swarm_belt` in `src/swarm.rs`.
#[inline(always)]
fn beyond_belt(q: SwarmQuery, inner: f32, outer: f32, spread: f32) -> bool {
    let pad = spread * (q.t1 - q.t0) * (q.t1 - q.t0);
    q.far_r < inner - pad || q.near_r > outer + pad
}

#[inline(always)]
fn safe_reciprocal(v: f32) -> f32 {
    if v.abs() < 1.0e-20 { 1.0e20 } else { 1.0 / v }
}

/// Whether the segment meets the box [lo, hi].
#[inline(always)]
fn segment_meets_box(q: SwarmQuery, inv: Vec3, lo: Vec3, hi: Vec3) -> bool {
    let a = (lo - q.start) * inv;
    let b = (hi - q.start) * inv;
    let near = a.x.min(b.x).max(a.y.min(b.y)).max(a.z.min(b.z)).max(0.0);
    let far = a.x.max(b.x).min(a.y.max(b.y)).min(a.z.max(b.z)).min(1.0);
    near <= far
}

/// The same result as `swarm_segment_hit`, testing only the bodies whose swept box
/// in the step's time slice meets the segment. Node i is `nodes[2i]` (box minimum,
/// then the right child or the first item) and `nodes[2i + 1]` (box maximum, then
/// 0 for an internal node or the item count); an internal node's left child follows
/// it. Steps outside the belt miss; other steps that fit no slice fall back to
/// brute force. With no slices this is plain brute force, the unfiltered reference.
#[cuda_device::device]
fn swarm_bvh_hit(
    start: Vec3,
    end: Vec3,
    t0: f32,
    t1: f32,
    swarm: *const SwarmBody,
    count: u32,
    nodes: *const Vec4,
    items: *const u32,
    roots: *const u32,
    slices: u32,
    belt: (f32, f32, f32),
) -> Vec4 {
    let q = swarm_query(start, end, t0, t1);
    if slices > 0 && beyond_belt(q, belt.0, belt.1, belt.2) {
        return vec4_splat(0.0);
    }
    let middle = -0.5 * (t0 + t1);
    let slice = (middle / SWARM_SLICE_WIDTH) as u32;
    if !(middle >= 0.0 && (t0 - t1).abs() <= SWARM_STEP_SPAN && slice < slices) {
        return swarm_segment_hit(start, end, t0, t1, swarm, count);
    }
    let inv = vec3(
        safe_reciprocal(q.segment.x),
        safe_reciprocal(q.segment.y),
        safe_reciprocal(q.segment.z),
    );
    let mut best = 2.0_f32;
    let mut result = vec4_splat(0.0);
    let mut stack = [0u32; 32];
    let mut depth = 1usize;
    stack[0] = unsafe { *roots.add(slice as usize) };
    while depth > 0 {
        depth -= 1;
        let node = stack[depth];
        let lo = unsafe { *nodes.add(2 * node as usize) };
        let hi = unsafe { *nodes.add(2 * node as usize + 1) };
        if !segment_meets_box(q, inv, lo.xyz(), hi.xyz()) {
            continue;
        }
        let link = lo.w.to_bits();
        let leaf_count = hi.w.to_bits();
        if leaf_count == 0 {
            stack[depth] = link;
            stack[depth + 1] = node + 1;
            depth += 2;
        } else {
            let mut k = 0u32;
            while k < leaf_count {
                let index = unsafe { *items.add((link + k) as usize) };
                swarm_body_hit(q, unsafe { *swarm.add(index as usize) }, &mut best, &mut result);
                k += 1;
            }
        }
    }
    result
}

#[inline(always)]
fn nt_temp(r_disk: f32, disk: &Disk) -> f32 {
    let ratio = disk.isco_r / r_disk;
    let sqrt_ratio = sqrt(ratio);
    let f = (1.0 - sqrt_ratio).max(0.0);
    sqrt_ratio * sqrt(sqrt_ratio) * sqrt(sqrt(f))
}

#[inline(always)]
fn blackbody_color(t: f32) -> Vec3 {
    let s = clamp_f32(t, 0.0, 1.0);
    if s < 0.4 {
        vec3(0.05, 0.0, 0.0).mix(vec3(1.0, 0.35, 0.02), s / 0.4)
    } else if s < 0.75 {
        vec3(1.0, 0.35, 0.02).mix(vec3(1.0, 0.95, 0.80), (s - 0.4) / 0.35)
    } else {
        vec3(1.0, 0.95, 0.80).mix(vec3(0.65, 0.80, 1.0), (s - 0.75) / 0.25)
    }
}

#[inline(always)]
fn disk_edge_fade(r_disk: f32, disk: &Disk) -> f32 {
    let edge_width = (0.06 * (disk.r2 - disk.r1)).max(0.35 * SCHWARZSCHILD_RADIUS);
    let inner = smoothstep(disk.r1, disk.r1 + edge_width, r_disk);
    let outer = 1.0 - smoothstep(disk.r2 - edge_width, disk.r2, r_disk);
    clamp_f32(inner * outer, 0.0, 1.0)
}

#[inline(always)]
fn get_h_over_r(r_disk: f32, disk: &Disk) -> f32 {
    if disk.model == 1 {
        let safe_r = r_disk.max(SCHWARZSCHILD_RADIUS * 1.0e-3);
        let safe_rt = disk.r_trunc.max(SCHWARZSCHILD_RADIUS * 1.0e-3);
        let t = clamp_f32((log(safe_r) - log(safe_rt)) / 0.4, -10.0, 10.0);
        let w = 0.5 * (1.0 + tanh(t));
        return w * disk.h_thin + (1.0 - w) * disk.h_hot;
    } else if disk.model == 2 {
        let r_puff = disk.r_trunc.max(SCHWARZSCHILD_RADIUS * 0.5);
        let ratio = r_disk / r_puff;
        return disk.h_thin + (disk.h_hot - disk.h_thin) / (1.0 + ratio * ratio);
    }
    disk.h_thin
}

#[inline(always)]
fn disk_midplane_y(r_disk: f32, horizontal: Vec2, disk: &Disk) -> f32 {
    if disk.model != 3 {
        return 0.0;
    }
    let r_bp_safe = disk.r_bp.max(SCHWARZSCHILD_RADIUS * 0.1);
    let ln_norm = clamp_f32(
        log(r_disk.max(SCHWARZSCHILD_RADIUS * 0.01) / r_bp_safe) / 0.5,
        -10.0,
        10.0,
    );
    let w = 0.5 * (1.0 + tanh(ln_norm));
    let beta = disk.tilt_deg * (PI / 180.0) * w;
    let gamma = disk.twist_deg * (PI / 180.0) * log(1.0 + r_disk / r_bp_safe);
    let rho2 = horizontal.dot(horizontal);
    if rho2 == 0.0 {
        return 0.0;
    }
    let g = sincos(gamma);
    let s = (horizontal.y * g.y - horizontal.x * g.x) / sqrt(rho2);
    r_disk * sincos(beta).x * s
}

#[inline(always)]
fn sub_keplerian_factor(h_r: f32) -> f32 {
    1.0 - 0.5 * clamp_f32(h_r * 2.0, 0.0, 1.0)
}

#[inline(always)]
fn hot_emissivity_t(r: f32, disk: &Disk) -> f32 {
    let r0 = disk.isco_r.max(disk.r1);
    pow(clamp_f32(r0 / r.max(r0), 0.0, 1.0), 0.6)
}

#[inline(always)]
fn tonemap(hdr: Vec3) -> Vec3 {
    let x = hdr.clamp(vec3_splat(0.0), vec3_splat(1.0e4));
    ((x * (2.51 * x + vec3_splat(0.03)))
        / (x * (2.43 * x + vec3_splat(0.59)) + vec3_splat(0.14)))
    .clamp(vec3_splat(0.0), vec3_splat(1.0))
}

const TAN_PI_8: f32 = 0.41421356237309503;

#[inline(always)]
fn atan_poly(u: f32) -> f32 {
    let u2 = u * u;
    u * (1.0
        + u2 * (-1.0 / 3.0
            + u2 * (1.0 / 5.0
                + u2 * (-1.0 / 7.0
                    + u2 * (1.0 / 9.0
                        + u2 * (-1.0 / 11.0
                            + u2 * (1.0 / 13.0
                                + u2 * (-1.0 / 15.0
                                    + u2 * (1.0 / 17.0
                                        + u2 * (-1.0 / 19.0
                                            + u2 * (1.0 / 21.0
                                                + u2 * (-1.0 / 23.0 + u2 * (1.0 / 25.0)))))))))))))
}

#[cuda_device::device]
fn atan2_arith(y: f32, x: f32) -> f32 {
    let ax = x.abs();
    let ay = y.abs();
    let hi = ax.max(ay);
    if hi == 0.0 {
        return 0.0;
    }
    let t = ax.min(ay) / hi;
    let mut a = atan_poly(t);
    if t > TAN_PI_8 {
        a = 0.25 * PI + atan_poly((t - 1.0) / (t + 1.0));
    }
    if ay > ax {
        a = 0.5 * PI - a;
    }
    if x < 0.0 {
        a = PI - a;
    }
    if y < 0.0 {
        a = -a;
    }
    a
}

#[inline(always)]
unsafe fn sample_skybox(dir: Vec3, skybox: *const Vec4, sky_w: i32, sky_h: i32) -> Vec3 {
    let rho2 = dir.xz().dot(dir.xz());
    let mut rho = 0.0;
    if rho2 > 0.0 {
        rho = sqrt(rho2);
    }
    let uv = vec2(
        atan2_arith(dir.z, dir.x) / (2.0 * PI) + 0.5,
        atan2_arith(rho, dir.y) / PI,
    );
    let texel_x = uv.x * (sky_w as f32) - 0.5;
    let texel_y = uv.y * (sky_h as f32) - 0.5;
    let base_x = floor_f32(texel_x) as i32;
    let base_y = floor_f32(texel_y) as i32;
    let weight_x = fract_f32(texel_x);
    let weight_y = fract_f32(texel_y);
    let x0 = ((base_x % sky_w) + sky_w) % sky_w;
    let x1 = (x0 + 1) % sky_w;
    let y0 = base_y.max(0).min(sky_h - 1);
    let y1 = (base_y + 1).max(0).min(sky_h - 1);
    let load = |x: i32, y: i32| unsafe { (*skybox.add((y * sky_w + x) as usize)).xyz() };
    let top = load(x0, y0).mix(load(x1, y0), weight_x);
    let bottom = load(x0, y1).mix(load(x1, y1), weight_x);
    top.mix(bottom, weight_y)
}

#[inline(always)]
fn heatmap_color(t: f32) -> Vec3 {
    vec3(
        clamp_f32(t * 3.0, 0.0, 1.0),
        clamp_f32(t * 3.0 - 1.0, 0.0, 1.0),
        clamp_f32(t * 3.0 - 2.0, 0.0, 1.0),
    )
}

#[derive(Clone, Copy, Default)]
pub struct Plasma {
    pub rgb: Vec3,
    pub j: Vec4,
    pub alpha: f32,
    pub rho: Vec3,
    pub energy: f32,
}

#[inline(always)]
fn projected_evpa(bx: f32, by: f32) -> Vec2 {
    vec2(by * by - bx * bx, -2.0 * bx * by) / (bx * bx + by * by).max(1.0e-12)
}

#[cuda_device::device]
fn sample_plasma(ray: Ray, objects: &Objects, cam: &Camera, disk: &Disk) -> Plasma {
    let mut plasma = Plasma::default();
    let r = disk_radius(ray.pos, disk.spin, disk.binary_enabled != 0);
    if r <= disk.r1 || r >= disk.r2 {
        return plasma;
    }
    let h_r = get_h_over_r(r, disk);
    let height = (h_r * r).max(1.0e-4);
    let z = (ray.pos.y - disk_midplane_y(r, ray.pos.xz(), disk)) / height;
    if z.abs() >= 4.0 {
        return plasma;
    }
    let (g, inv) = plasma_metric(ray.pos, objects);
    let density = 0.4 * exp(-0.5 * z * z) * disk_edge_fade(r, disk) / height;
    let k = inv * ray.p;
    let omega = sub_keplerian_factor(h_r) / (r * sqrt(r) + disk.spin).max(1.0e-3);
    let tangent = vec3(ray.pos.z, 0.0, -ray.pos.x);
    let mut fluid = vec4_f_v3(1.0, omega * tangent);
    let norm = fluid.dot(g * fluid);
    if norm < -1.0e-4 {
        fluid *= inverse_sqrt(-norm);
    } else {
        let lapse = inverse_sqrt(-inv[0][0]);
        fluid = -lapse * inv[0];
    }
    plasma.energy = ray.p.dot(fluid).max(1.0e-5);
    let redshift = clamp_f32(1.0 / plasma.energy, 0.01, 20.0);
    let boost = redshift * redshift * redshift;
    plasma.alpha = 0.7 * density;
    // Thermal intensity does not depend on the magnetic field or polarization frame.
    if cam.polarization_view == 0 && disk.model != 1 {
        plasma.rgb = density * boost * blackbody_color(nt_temp(r, disk) / 0.488);
        return plasma;
    }
    let freq_ratio = 230.0 / (cam.frequency_ghz / redshift).max(1.0);
    let frame = screen_frame_at(ray, g, inv);
    let mut e1 = vec4_f_v3(0.0, frame[0]);
    let mut e2 = vec4_f_v3(0.0, frame[1]);
    e1 -= k * (e1.dot(g * fluid) / plasma.energy);
    e2 -= k * (e2.dot(g * fluid) / plasma.energy);
    let mut b = vec4_f_v3(0.0, tangent.normalize());
    b += fluid * b.dot(g * fluid);
    b *= inverse_sqrt(b.dot(g * b).max(1.0e-12));
    let bx = b.dot(g * e1);
    let by = b.dot(g * e2);
    let perpendicular2 = clamp_f32(bx * bx + by * by, 0.0, 1.0);
    let mut hot = 0.0;
    if disk.model == 1 {
        hot = 0.5
            * (1.0 - tanh(clamp_f32(log(r / disk.r_trunc.max(0.001)) / 0.4, -10.0, 10.0)));
    }
    let thermal = (1.0 - hot) * blackbody_color(nt_temp(r, disk) / 0.488);
    let synch =
        hot * hot_emissivity_t(r, disk) * perpendicular2 * freq_ratio * vec3(1.0, 0.65, 0.3);
    plasma.rgb = density * boost * (thermal + synch);
    if cam.polarization_view == 0 {
        return plasma;
    }
    let evpa = projected_evpa(bx, by);
    let bparallel = -b.dot(g * k) / plasma.energy;
    let luma = vec3(0.2126, 0.7152, 0.0722);
    let intensity = plasma.rgb.dot(luma);
    let synch_i = density * boost * synch.dot(luma);
    plasma.j = vec4_f_v2_f(intensity, 0.75 * synch_i * evpa, 0.0);
    let rotation = 2.0 * cam.faraday_depth * density * bparallel * freq_ratio * freq_ratio;
    let conversion = cam.conversion_depth * density * perpendicular2
        * (freq_ratio * freq_ratio * freq_ratio);
    plasma.rho = vec3_v2_f(conversion * evpa, rotation);
    plasma
}

#[inline(always)]
fn polarization_color(stokes: Vec4, cam: &Camera) -> Vec3 {
    if stokes.x <= 1.0e-8 {
        return vec3_splat(0.0);
    }
    let pol = (stokes.yzw() / stokes.x).clamp(vec3_splat(-1.0), vec3_splat(1.0));
    if cam.polarization_view == 1 {
        return vec3_splat(clamp_f32(pol.xy().length(), 0.0, 1.0));
    }
    if cam.polarization_view == 2 {
        let rho2 = pol.xy().dot(pol.xy());
        if rho2 == 0.0 {
            return vec3_splat(0.0);
        }
        let rho = sqrt(rho2);
        let unit = pol.xy() / rho;
        let hue = vec3_splat(0.5)
            + 0.5
                * vec3(
                    unit.x,
                    -0.5 * unit.x + SQRT3_2 * unit.y,
                    -0.5 * unit.x - SQRT3_2 * unit.y,
                );
        return hue * clamp_f32(rho, 0.0, 1.0);
    }
    let mut signed = pol.z;
    if cam.polarization_view == 3 {
        signed = pol.x;
    }
    if cam.polarization_view == 4 {
        signed = pol.y;
    }
    let color = if signed >= 0.0 {
        vec3(1.0, 0.25, 0.1)
    } else {
        vec3(0.15, 0.4, 1.0)
    };
    signed.abs() * color
}

#[inline(always)]
fn byte_u8(v: f32) -> u32 {
    (clamp_f32(v, 0.0, 1.0) * 255.0 + 0.5) as u32
}

#[inline(always)]
fn pack_rgba8(c: Vec4) -> u32 {
    byte_u8(c.x) | (byte_u8(c.y) << 8) | (byte_u8(c.z) << 16) | (byte_u8(c.w) << 24)
}

// -- Production Kernels ------------------------------------------------------

const EARLY_CAPTURE_CLEARANCE: f32 = 0.5;

#[inline(always)]
fn vacuum_radius_sq(objects: &Objects, disk: &Disk) -> f32 {
    let body = objects.pos_radius[0];
    if objects.num_objects != 1 || disk.binary_enabled != 0 || objects.mass[0].x != 1.0
        || body.x != 0.0 || body.y != 0.0 || body.z != 0.0
    {
        return f32::INFINITY;
    }
    // The projected Kerr disk radius obeys rho² <= r_disk² + spin².
    let radius_sq = disk.r2 * disk.r2 + disk.spin * disk.spin;
    let aspect = if disk.model == 1 || disk.model == 2 {
        disk.h_thin.max(disk.h_hot)
    } else {
        disk.h_thin
    };
    let warp = if disk.model == 3 { 1.01 * disk.r2 } else { 0.0 };
    let height = 4.0 * (aspect * disk.r2).max(1.0e-4) + warp;
    (1.02 * (radius_sq + height * height)).max(body.w * body.w).max(64.0 * 64.0)
}

#[inline(always)]
fn far_field_distance(pos: Vec3, velocity: Vec3, speed: f32, vacuum_sq: f32) -> f32 {
    let radius_sq = pos.dot(pos);
    if radius_sq <= vacuum_sq {
        return 0.0;
    }
    let radius = sqrt(radius_sq);
    if pos.dot(velocity) <= 0.95 * radius * speed {
        return 0.0;
    }
    // Return to the ordinary cap before the sampling sphere.
    (0.28 * radius).min(192.0).min((ESCAPE_R - 64.0 - radius).max(0.0))
}

#[inline(always)]
fn supports_early_capture(objects: &Objects, disk: &Disk) -> bool {
    let position = objects.pos_radius[0];
    let spin = objects.spin[0];
    let color = objects.color[0];
    objects.num_objects == 1
        && disk.binary_enabled == 0
        && objects.mass[0].x == 1.0
        && position.x == 0.0 && position.y == 0.0 && position.z == 0.0
        && color.x == 0.0 && color.y == 0.0 && color.z == 0.0
        && spin.x == 0.0 && spin.z == 0.0 && spin.y == disk.spin
        && disk.spin.abs() <= 0.995
}

/// The next binary64 value above `x`; NaN and +inf are returned unchanged.
#[inline(always)]
fn ulp_up(x: f64) -> f64 {
    if !(x < f64::INFINITY) {
        x
    } else if x == 0.0 {
        f64::from_bits(1)
    } else if x > 0.0 {
        f64::from_bits(x.to_bits() + 1)
    } else {
        f64::from_bits(x.to_bits() - 1)
    }
}

#[inline(always)]
fn ulp_down(x: f64) -> f64 {
    -ulp_up(-x)
}

/// Closed binary64 interval for the early-capture guard. Each operation rounds to
/// nearest with an explicit `_rn` intrinsic, so nothing is contracted into an FMA,
/// then steps one ulp outward. IEEE 754 round-to-nearest is within half an ulp, so
/// the result encloses the exact real value. `src/certified/capture.rs` repeats the
/// guard with exact-dyadic-checked intervals on the CPU.
#[derive(Clone, Copy)]
struct Bound {
    lo: f64,
    hi: f64,
}

impl Bound {
    #[inline(always)]
    fn point(x: f64) -> Self {
        Bound { lo: x, hi: x }
    }

    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Bound {
            lo: ulp_down(cuda_device::float::add_rn_f64(self.lo, o.lo)),
            hi: ulp_up(cuda_device::float::add_rn_f64(self.hi, o.hi)),
        }
    }

    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        self.add(Bound { lo: -o.hi, hi: -o.lo })
    }

    #[inline(always)]
    fn hull(p: [f64; 4]) -> Self {
        Bound {
            lo: ulp_down(p[0].min(p[1]).min(p[2].min(p[3]))),
            hi: ulp_up(p[0].max(p[1]).max(p[2].max(p[3]))),
        }
    }

    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        use cuda_device::float::mul_rn_f64 as m;
        Self::hull([m(self.lo, o.lo), m(self.lo, o.hi), m(self.hi, o.lo), m(self.hi, o.hi)])
    }

    /// Requires a divisor that excludes zero; the guard checks that first.
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        use cuda_device::float::div_rn_f64 as d;
        // n / d = (-n) / (-d), so take a positive divisor; then two quotients suffice.
        let (n, o) = if o.lo > 0.0 { (self, o) } else { (Bound { lo: -self.hi, hi: -self.lo }, Bound { lo: -o.hi, hi: -o.lo }) };
        let lo = if n.lo >= 0.0 { d(n.lo, o.hi) } else { d(n.lo, o.lo) };
        let hi = if n.hi >= 0.0 { d(n.hi, o.lo) } else { d(n.hi, o.hi) };
        Bound { lo: ulp_down(lo), hi: ulp_up(hi) }
    }

    #[inline(always)]
    fn sq(self) -> Self {
        let a = cuda_device::float::mul_rn_f64(self.lo, self.lo);
        let b = cuda_device::float::mul_rn_f64(self.hi, self.hi);
        if self.lo >= 0.0 {
            Bound { lo: ulp_down(a).max(0.0), hi: ulp_up(b) }
        } else if self.hi <= 0.0 {
            Bound { lo: ulp_down(b).max(0.0), hi: ulp_up(a) }
        } else {
            Bound { lo: 0.0, hi: ulp_up(a.max(b)) }
        }
    }

    /// For an argument whose exact value is nonnegative.
    #[inline(always)]
    fn sqrt(self) -> Self {
        Bound {
            lo: ulp_down(cuda_device::float::sqrt_rn_f64(self.lo.max(0.0))).max(0.0),
            hi: ulp_up(cuda_device::float::sqrt_rn_f64(self.hi.max(0.0))),
        }
    }
}

// Kept out of line: inlined into the render loop it costs about 0.8 ms per frame.
#[cuda_device::device]
#[inline(never)]
fn inward_kerr_capture(ray: Ray, velocity: Vec3, spin: f32, disk_inner: f32) -> bool {
    // Fast binary64 estimate with margins; a ray it accepts must then pass the interval
    // certificate, which runs once per captured ray (f64 is slow on consumer GPUs).
    let a = f64::from(spin);
    let a2 = a * a;
    let horizon = 1.0 + cuda_device::float::sqrt_rn_f64(1.0 - a2);
    let x = f64::from(ray.pos.x);
    let y = f64::from(ray.pos.y);
    let z = f64::from(ray.pos.z);
    let rho2 = x * x + z * z;
    let q = rho2 + y * y - a2;
    let r2 = 0.5 * (q + cuda_device::float::sqrt_rn_f64(q * q + 4.0 * a2 * y * y));
    let r = cuda_device::float::sqrt_rn_f64(r2);
    // The projected disk radius is at most the Kerr radius. Keep a gap from the emissivity cutoff.
    if !(r > horizon && r + 0.05 < f64::from(disk_inner) && ray.p.x > 1.0e-5) {
        return false;
    }

    let sine = cuda_device::float::sqrt_rn_f64(rho2 / (r2 + a2));
    if !(sine > 0.1) {
        return false;
    }
    let cosine = y / r;
    let energy = -f64::from(ray.p.x);
    let px = f64::from(ray.p.y);
    let py = f64::from(ray.p.z);
    let pz = f64::from(ray.p.w);
    let lambda = (z * px - x * pz) / energy;
    // At fixed Kerr radius, the Kerr-Schild to Boyer-Lindquist shifts are constant.
    let polar = ((cosine / sine) * (x * px + z * pz) - r * sine * py) / energy;
    let azimuthal = lambda / sine - a * sine;
    let carter = polar * polar + azimuthal * azimuthal;
    let sigma_dr = r
        * (x * f64::from(velocity.x) + (1.0 + a2 / r2) * y * f64::from(velocity.y)
            + z * f64::from(velocity.z)) / energy.abs();
    let horizon_p = horizon * horizon + a2 - a * lambda;
    let here_p = r2 + a2 - a * lambda;
    let barrier = (r - horizon) * (r + horizon - 2.0) * carter;
    let scale = 1.0 + here_p * here_p + barrier;
    let radial = here_p * here_p - barrier;
    // P(s) increases and Delta(s) <= Delta(r) for horizon <= s <= r.
    // Require a positive lower bound on R throughout that interval and a consistent inward tangent.
    horizon_p > 0.0
        && horizon_p * horizon_p - barrier > 0.02 * scale
        && sigma_dr < -0.05 * r2
        && (sigma_dr * sigma_dr - radial).abs() < 0.004 * scale
        && kerr_capture_certified(ray, spin, disk_inner)
}

/// The capture guard's hypotheses for the exact real values of the stored binary32
/// state, in interval binary64: r between the horizon and `disk_inner`, P(h) > 0,
/// P(h)^2 - Delta(r) K > 0 (`null_radial_positive_below` in KerrCapture.lean) and an
/// inward tangent computed from the state's own momentum. Mirrors
/// `black_hole::certified::capture_certified`. Finite f32 inputs, with p_t > 1e-5,
/// sine > 0.1 and r > 1 before their divisions, keep every intermediate below 1e300,
/// so no endpoint overflows.
#[cuda_device::device]
fn kerr_capture_certified(ray: Ray, spin: f32, disk_inner: f32) -> bool {
    let finite = |v: f32| v.abs() < f32::INFINITY;
    if !(finite(ray.pos.x) && finite(ray.pos.y) && finite(ray.pos.z)
        && finite(ray.p.y) && finite(ray.p.z) && finite(ray.p.w) && finite(disk_inner)
        && ray.p.x < f32::INFINITY && ray.p.x > 1.0e-5)
    {
        return false;
    }
    let point = |v: f32| Bound::point(f64::from(v));
    let one = Bound::point(1.0);
    let a = point(spin);
    let a2 = a.sq();
    let horizon = one.add(one.sub(a2).sqrt());
    let (x, y, z) = (point(ray.pos.x), point(ray.pos.y), point(ray.pos.z));
    let rho2 = x.sq().add(z.sq());
    let y2 = y.sq();
    let q = rho2.add(y2).sub(a2);
    let r2 = q.add(q.sq().add(Bound::point(4.0).mul(a2).mul(y2)).sqrt()).mul(Bound::point(0.5));
    let r = r2.sqrt();
    if !(r.lo > horizon.hi && r.hi < f64::from(disk_inner)) {
        return false;
    }
    let r2a2 = r2.add(a2);
    let sine = rho2.div(r2a2).sqrt();
    if !(sine.lo > 0.1) {
        return false;
    }
    // E = -p_t < 0 for the backward ray, and |E| = p_t.
    let pt = point(ray.p.x);
    let energy = Bound::point(-f64::from(ray.p.x));
    let (px, py, pz) = (point(ray.p.y), point(ray.p.z), point(ray.p.w));
    let lambda = z.mul(px).sub(x.mul(pz)).div(energy);
    let polar = y.div(r).div(sine).mul(x.mul(px).add(z.mul(pz))).sub(r.mul(sine).mul(py)).div(energy);
    let azimuthal = lambda.div(sine).sub(a.mul(sine));
    let carter = polar.sq().add(azimuthal.sq());
    let horizon_p = horizon.sq().add(a2).sub(a.mul(lambda));
    let barrier = r.sub(horizon).mul(r.add(horizon).sub(Bound::point(2.0))).mul(carter);
    // Sigma dr/dlambda: g^-1 = eta - 2h l#l#^T with l# = (-1, l), exact for the null l of
    // add_kerr with spin along +y.
    let h = r.mul(r2).div(r2.sq().add(a.mul(y).sq()));
    let lx = r.mul(x).sub(a.mul(z)).div(r2a2);
    let ly = y.div(r);
    let lz = r.mul(z).add(a.mul(x)).div(r2a2);
    let k = Bound::point(2.0).mul(h).mul(lx.mul(px).add(ly.mul(py)).add(lz.mul(pz)).sub(pt));
    let (vx, vy, vz) = (px.sub(k.mul(lx)), py.sub(k.mul(ly)), pz.sub(k.mul(lz)));
    let sigma_dr =
        r.mul(x.mul(vx).add(one.add(a2.div(r2)).mul(y).mul(vy)).add(z.mul(vz))).div(pt);
    horizon_p.lo > 0.0 && horizon_p.sq().sub(barrier).lo > 0.0 && sigma_dr.hi < 0.0
}

#[cuda_device::kernel]
pub unsafe fn bh_wormhole(
    out_image: *mut Vec4, cam: *const Camera,
    near_sky: *const Vec4, far_sky: *const Vec4,
    width: u32, height: u32, near_w: u32, near_h: u32, far_w: u32, far_h: u32,
    matter_time: f32, matter_enabled: u32,
) {
    let x = gid_x();
    let y = gid_y();
    if x >= width || y >= height { return; }
    let cam = unsafe { &*cam };
    let a = cam.wormhole_radius;
    let l = cam.pos.length();
    let normal = cam.pos / l;
    let u = (2.0 * (x as f32 + 0.5 + cam.jitter_x) / width as f32 - 1.0) * cam.aspect * cam.tan_half_fov;
    let v = (1.0 - 2.0 * (y as f32 + 0.5 + cam.jitter_y) / height as f32) * cam.tan_half_fov;
    let sight = (u * cam.right - v * cam.up + cam.forward).normalize();
    let p = sight.dot(normal);
    let transverse = sight - p * normal;
    let transverse_norm = transverse.length();
    let tangent = if transverse_norm > 1e-8 { transverse / transverse_norm } else { cam.right };
    // Local orthonormal camera components, not coordinate components.
    let impact = sqrt(l*l + a*a) * transverse_norm;
    let observer_time = if matter_enabled != 0 { Some(matter_time) } else { None };
    let output = match ellis::trace(l, p, impact, a, cam.max_iter, observer_time) {
        Some((state, steps, intensity)) => {
            let sc = sincos(state[2]);
            let radial = sc.y * normal + sc.x * tangent;
            let angular = -sc.x * normal + sc.y * tangent;
            // Asymptotic Cartesian velocity retains the finite-cutoff angular tail.
            let direction = (state[0] * state[1] * radial + impact * angular).normalize();
            let sky = unsafe {
                if state[0] < 0.0 { sample_skybox(direction, far_sky, far_w as i32, far_h as i32) }
                else { sample_skybox(direction, near_sky, near_w as i32, near_h as i32) }
            };
            if cam.debug_heatmap != 0 { heatmap_color(steps as f32 / cam.max_iter.max(1) as f32) }
            else { tonemap(sky + 0.2 * intensity * vec3(1.0, 0.45, 0.12)) }
        }
        None => vec3(1.0, 0.0, 1.0),
    };
    unsafe { *out_image.add((y * width + x) as usize) = vec4_v3_f(output, 1.0); }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_wormhole(cases: *const Vec4, results: *mut Vec4, count: u32) {
    let i = gid_x();
    if i >= count { return; }
    let input = unsafe { *cases.add(i as usize) };
    let rhs = ellis::rhs([input.x, input.y, 0.0], input.z, input.w);
    let ray = match ellis::trace(input.x, input.y, input.z, input.w, 10_000, None) {
        Some((s, steps, _)) => vec4(s[0], s[1], s[2], steps as f32),
        None => vec4(0.0, 0.0, 0.0, -1.0),
    };
    unsafe {
        *results.add(2 * i as usize) = vec4(rhs[0], rhs[1], rhs[2], 0.0);
        *results.add(2 * i as usize + 1) = ray;
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_dust(cases: *const Vec4, results: *mut Vec4, count: u32) {
    let i = gid_x();
    if i >= count { return; }
    let c = unsafe { *cases.add(i as usize) };
    let density = ellis::dust_density(c.x, c.y, c.w);
    let energy = ellis::dust_photon_energy(c.z);
    let ray = match ellis::trace(c.x, c.z, 0.0, c.w, 10_000, Some(c.y)) {
        Some((s, _, intensity)) => vec4(s[0],s[1],s[2],intensity),
        None => vec4(0.0,0.0,0.0,-1.0),
    };
    unsafe {
        *results.add(2*i as usize) = vec4(density, (c.x*c.x+c.w*c.w)*density, energy*energy, 0.0);
        *results.add(2*i as usize+1) = ray;
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_geodesic(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
) {
    unsafe {
        render_geodesic::<false, false, GENERIC, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h,
            core::ptr::null_mut(), true, true, true, true, 0,
            gid_x(), gid_y(), no_swarm,
        );
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_geodesic_full_trace(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
) {
    unsafe {
        render_geodesic::<false, false, GENERIC, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h,
            core::ptr::null_mut(), false, true, true, true, 0,
            gid_x(), gid_y(), no_swarm,
        );
    }
}

/// `bh_geodesic` for a scene with exactly one source (checklist P1.2).
#[cuda_device::kernel]
pub unsafe fn bh_geodesic_single(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
) {
    unsafe {
        render_geodesic::<false, false, SINGLE, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h,
            core::ptr::null_mut(), true, true, true, true, 0,
            gid_x(), gid_y(), no_swarm,
        );
    }
}

/// `bh_geodesic_single` for thermal intensity alone: no polarization view and no hot
/// flow, so `sample_plasma` never reads the screen vector (checklist P1.2).
#[cuda_device::kernel]
pub unsafe fn bh_geodesic_scalar(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
) {
    unsafe {
        render_geodesic::<false, false, SINGLE_SCALAR, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h,
            core::ptr::null_mut(), true, true, true, true, 0,
            gid_x(), gid_y(), no_swarm,
        );
    }
}

/// Any combination of the ray options: bit 0 the full trace instead of guarded early
/// capture, bit 1 capped steps instead of far-field steps (checklist P1.8), bit 2 the
/// legacy step-doubling RK4 controller
/// instead of Dormand–Prince, bit 3 the legacy coupled transfer (one midpoint cell per
/// geodesic step, the step limited by the disk) instead of decoupled transfer (checklist
/// P1.9), bits 4-7 a shift that divides the disk transfer cell length by 2^shift.
#[cuda_device::kernel]
pub unsafe fn bh_geodesic_experiments(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
    experiments: u32,
) {
    unsafe {
        render_geodesic::<false, false, GENERIC, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h,
            core::ptr::null_mut(), experiments & 1 == 0, experiments & 2 == 0, experiments & 4 == 0,
            experiments & 8 == 0, (experiments >> 4) & 15,
            gid_x(), gid_y(), no_swarm,
        );
    }
}

/// The production renderer with a swarm of moving bodies, tested by brute force.
#[cuda_device::kernel]
pub unsafe fn bh_geodesic_swarm(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
    swarm: *const SwarmBody,
    swarm_count: u32,
    bvh_nodes: *const Vec4,
    bvh_items: *const u32,
    bvh_roots: *const u32,
    bvh_slices: u32,
    belt_inner: f32,
    belt_outer: f32,
    belt_spread: f32,
    experiments: u32,
) {
    unsafe {
        render_geodesic::<false, true, GENERIC, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h,
            core::ptr::null_mut(), experiments & 1 == 0, experiments & 2 == 0, experiments & 4 == 0, experiments & 8 == 0, 0,
            gid_x(), gid_y(),
            |start, end, t0, t1, _| swarm_bvh_hit(
                start, end, t0, t1, swarm, swarm_count, bvh_nodes, bvh_items, bvh_roots, bvh_slices,
                (belt_inner, belt_outer, belt_spread),
            ),
        );
    }
}

#[inline(always)]
fn atomic_add_u32(address: *mut u32, value: u32) -> u32 {
    let address = address as u64;
    let old: u32;
    unsafe {
        cuda_device::ptx_asm!("atom.global.add.u32 %0, [%1], %2;", out("=r") old, in("l") address, in("r") value)
    };
    old
}

#[inline(always)]
fn atomic_max_u32(address: *mut u32, value: u32) {
    let address = address as u64;
    unsafe { cuda_device::ptx_asm!("red.global.max.u32 [%0], %1;", in("l") address, in("r") value) };
}

/// First pass of the OptiX swarm renderer: renders rows from `row0` as
/// `bh_geodesic_swarm` would, except that steps which may meet the belt are queued
/// instead of tested. Entry e holds
/// the step in `queue[2e..2e + 2]` as (start, t0), (end, t1), and the pixel state
/// before it in `states[3e..3e + 3]` as (rgb, transmission), stokes, (pixel,
/// iterations) bits. Steps outside the belt miss. Steps outside OptiX's time window,
/// and steps past `capacity`, are tested here by brute force; `counter` still counts
/// every queued step.
#[cuda_device::kernel]
pub unsafe fn bh_geodesic_swarm_record(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
    row0: u32,
    swarm: *const SwarmBody,
    swarm_count: u32,
    queue: *mut Vec4,
    states: *mut Vec4,
    counter: *mut u32,
    capacity: u32,
    belt_inner: f32,
    belt_outer: f32,
    belt_spread: f32,
    experiments: u32,
) {
    let (x, y) = (gid_x(), gid_y() + row0);
    let pixel = y * width + x;
    unsafe {
        render_geodesic::<false, true, GENERIC, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h,
            core::ptr::null_mut(), experiments & 1 == 0, experiments & 2 == 0, experiments & 4 == 0, experiments & 8 == 0, 0,
            x, y,
            |start, end, t0, t1, state| {
                if beyond_belt(swarm_query(start, end, t0, t1), belt_inner, belt_outer, belt_spread) {
                    return vec4_splat(0.0);
                }
                let middle = -0.5 * (t0 + t1);
                if !(middle >= 0.0
                    && (t0 - t1).abs() <= SWARM_STEP_SPAN
                    && middle < SWARM_SLICE_WIDTH * SWARM_SLICES)
                {
                    return swarm_segment_hit(start, end, t0, t1, swarm, swarm_count);
                }
                let slot = atomic_add_u32(counter, 1);
                if slot >= capacity {
                    return swarm_segment_hit(start, end, t0, t1, swarm, swarm_count);
                }
                let e = slot as usize;
                *queue.add(2 * e) = vec4_v3_f(start, t0);
                *queue.add(2 * e + 1) = vec4_v3_f(end, t1);
                *states.add(3 * e) = vec4_v3_f(state.rgb, state.transmission);
                *states.add(3 * e + 1) = state.stokes;
                *states.add(3 * e + 2) =
                    vec4(f32::from_bits(pixel), f32::from_bits(state.iterations), 0.0, 0.0);
                vec4_splat(0.0)
            },
        );
    }
}

/// Marks each pixel's earliest queued hit: `first[pixel]` = u32::MAX - iterations,
/// so a zeroed buffer means none.
#[cuda_device::kernel]
pub unsafe fn bh_swarm_first_hit(results: *const Vec4, states: *const Vec4, first: *mut u32, count: u32) {
    let e = gid_x() as usize;
    if e >= count as usize || unsafe { (*results.add(e)).w } <= 0.0 {
        return;
    }
    let tag = unsafe { *states.add(3 * e + 2) };
    atomic_max_u32(unsafe { first.add(tag.x.to_bits() as usize) }, u32::MAX - tag.y.to_bits());
}

/// Rewrites each pixel whose earliest swarm hit was a queued step, as
/// `render_geodesic` would have finished it there.
#[cuda_device::kernel]
pub unsafe fn bh_swarm_apply(
    out_image: *mut Vec4,
    cam: *const Camera,
    results: *const Vec4,
    states: *const Vec4,
    first: *const u32,
    count: u32,
) {
    let e = gid_x() as usize;
    if e >= count as usize {
        return;
    }
    let body = unsafe { *results.add(e) };
    let tag = unsafe { *states.add(3 * e + 2) };
    let (pixel, iterations) = (tag.x.to_bits() as usize, tag.y.to_bits());
    if body.w <= 0.0 || unsafe { *first.add(pixel) } != u32::MAX - iterations {
        return;
    }
    let lit = unsafe { *states.add(3 * e) };
    let mut stokes = unsafe { *states.add(3 * e + 1) };
    let transmission = lit.w;
    // The same arithmetic as the hit in `render_geodesic`.
    let rgb = lit.xyz() + transmission * body.xyz();
    stokes.x += transmission * body.xyz().dot(vec3(0.2126, 0.7152, 0.0722));
    unsafe { *out_image.add(pixel) = vec4_v3_f(pixel_output(rgb, stokes, iterations, &*cam), 1.0) };
}

/// Each case is two Vec4s, (start, t0) and (end, t1); the result is the hit colour and flag.
#[cuda_device::kernel]
pub unsafe fn bh_test_swarm_segment(
    cases: *const Vec4,
    swarm: *const SwarmBody,
    swarm_count: u32,
    results: *mut Vec4,
    count: u32,
) {
    let i = gid_x();
    if i >= count {
        return;
    }
    let start = unsafe { *cases.add(2 * i as usize) };
    let end = unsafe { *cases.add(2 * i as usize + 1) };
    unsafe {
        *results.add(i as usize) =
            swarm_segment_hit(start.xyz(), end.xyz(), start.w, end.w, swarm, swarm_count);
    }
}

// The profile CSV uses the same field order.
#[repr(C)]
#[derive(Default)]
pub struct RayDiagnostics {
    iterations: u32,
    steps: u32,
    rejected_attempts: u32,
    near_horizon_steps: u32,
    far_field_steps: u32,
    disk_limited_steps: u32,
    controller_limited_steps: u32,
    exit: u32,
    wide_steps: u32,
    sky_direction: [f32; 3],
    plasma_steps: u32,
    vacuum_disk_steps: u32,
    stokes: [f32; 4],
}

#[repr(u32)]
enum RayExit {
    IterationLimit,
    InvalidCamera,
    InvalidMetric,
    Horizon,
    StepRejected,
    AffineStagnation,
    ObjectHit,
    Escaped,
    Opaque,
    EarlyCapture,
    /// Captured or escaped inside the unresolved band.
    NearCritical,
}

#[cuda_device::kernel]
pub unsafe fn bh_geodesic_diagnostics(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
    diagnostics: *mut RayDiagnostics,
    experiments: u32,
) {
    unsafe {
        render_geodesic::<true, false, GENERIC, _>(
            out_image, cam, disk, objects, skybox, width, height, sky_w, sky_h, diagnostics,
            experiments & 1 == 0, experiments & 2 == 0, experiments & 4 == 0,
            experiments & 8 == 0, (experiments >> 4) & 15,
            gid_x(), gid_y(), no_swarm,
        );
    }
}

#[inline(always)]
fn advance_render_ray<const DIAGNOSTICS: bool, const PATH: u8>(
    ray: Ray, h: f32, metric: &mut Metric, objects: &Objects, stats: &mut RayDiagnostics,
    dormand_prince: bool,
) -> AdaptiveStep {
    if dormand_prince {
        advance_ray_dp45::<DIAGNOSTICS, PATH>(ray, h, metric, false, objects, &mut stats.rejected_attempts)
    } else if DIAGNOSTICS {
        advance_ray_counting::<true>(ray, h, metric, false, objects, &mut stats.rejected_attempts)
    } else {
        advance_ray_gauge(ray, h, metric, false, objects)
    }
}

/// A swarm query that never hits, for kernels without a swarm.
#[inline(always)]
fn no_swarm(_: Vec3, _: Vec3, _: f32, _: f32, _: PixelState) -> Vec4 {
    vec4_splat(0.0)
}

/// A pixel's accumulated light before a step, which a swarm hit there would end.
#[derive(Clone, Copy)]
struct PixelState {
    rgb: Vec3,
    transmission: f32,
    stokes: Vec4,
    iterations: u32,
}

/// The pixel colour for the light a ray gathered.
#[inline(always)]
fn pixel_output(rgb: Vec3, stokes: Vec4, iterations: u32, cam: &Camera) -> Vec3 {
    let mut output = tonemap(rgb);
    if cam.polarization_view != 0 {
        output = polarization_color(stokes, cam);
    }
    if cam.debug_heatmap != 0 {
        output = heatmap_color(iterations as f32 / cam.max_iter.max(1) as f32);
    }
    output
}

/// The coordinate direction of pixel (`pix_x`, `pix_y`) before the camera tetrad.
#[inline(always)]
fn pixel_direction(cam: &Camera, pix_x: u32, pix_y: u32, width: u32, height: u32) -> Vec3 {
    let u = (2.0 * (pix_x as f32 + 0.5 + cam.jitter_x) / width as f32 - 1.0)
        * cam.aspect
        * cam.tan_half_fov;
    let v = (1.0 - 2.0 * (pix_y as f32 + 0.5 + cam.jitter_y) / height as f32) * cam.tan_half_fov;
    (u * cam.right - v * cam.up + cam.forward).normalize()
}

/// The initial ray `render_geodesic` traces for pixel (`x`, `y`) of a `z`×`w` image:
/// position, momentum and screen vector, so host references can start from it.
#[cuda_device::kernel]
pub unsafe fn bh_test_pixel_ray(
    cam: *const Camera,
    objects: *const Objects,
    pixels: *const Vec4,
    results: *mut Vec4,
    count: u32,
) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let cam = unsafe { &*cam };
    let objects = unsafe { &*objects };
    let c = unsafe { *pixels.add(id as usize) };
    let dir = pixel_direction(cam, c.x as u32, c.y as u32, c.z as u32, c.w as u32);
    let ray = init_ray(cam.pos, dir, scene_metric(cam.pos, objects), cam);
    let base = (3 * id) as usize;
    unsafe {
        *results.add(base) = vec4_v3_f(ray.pos, 0.0);
        *results.add(base + 1) = ray.p;
        *results.add(base + 2) = ray.screen;
    }
}

/// Runs `inward_kerr_capture` on arbitrary states around a unit-mass Kerr hole at the
/// origin, two `Vec4` per case: (position, spin) and p. Writes 1 where it captures.
#[cuda_device::kernel]
pub unsafe fn bh_test_capture_guard(
    cases: *const Vec4,
    disk_inner: f32,
    results: *mut u32,
    count: u32,
) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let base = (2 * id) as usize;
    let (head, p) = unsafe { (*cases.add(base), *cases.add(base + 1)) };
    let ray = Ray { pos: head.xyz(), p, screen: vec4(0.0, 0.0, 0.0, 0.0) };
    let metric = add_kerr(flat_metric(), ray.pos, 1.0, vec3(0.0, head.w, 0.0));
    let velocity = (metric.inv * ray.p).yzw();
    unsafe {
        *results.add(id as usize) =
            if inward_kerr_capture(ray, velocity, head.w, disk_inner) { 1 } else { 0 };
    }
}

/// Renders pixel (`pix_x`, `pix_y`). With SWARM, `swarm_hit(start, end, t0, t1, state)`
/// tests each accepted step against the swarm, as `swarm_segment_hit` does.
#[inline(always)]
unsafe fn render_geodesic<
    const DIAGNOSTICS: bool,
    const SWARM: bool,
    const PATH: u8,
    F: Fn(Vec3, Vec3, f32, f32, PixelState) -> Vec4,
>(
    out_image: *mut Vec4,
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    skybox: *const Vec4,
    width: u32,
    height: u32,
    sky_w: u32,
    sky_h: u32,
    diagnostics: *mut RayDiagnostics,
    early_capture: bool,
    far_field: bool,
    dormand_prince: bool,
    decoupled: bool,
    refine: u32,
    pix_x: u32,
    pix_y: u32,
    swarm_hit: F,
) {
    if pix_x >= width || pix_y >= height {
        return;
    }
    let cam = unsafe { &*cam };
    let disk = unsafe { &*disk };
    let objects = unsafe { &*objects };
    let idx = (pix_y * width + pix_x) as usize;
    // Hermite dense output needs the Dormand–Prince stage rates.
    let decoupled = decoupled && dormand_prince;

    let dir = pixel_direction(cam, pix_x, pix_y, width, height);
    let mut metric = scene_metric(cam.pos, objects);
    let mut stats = RayDiagnostics::default();
    let mut exit = RayExit::IterationLimit;
    if !metric.valid || metric.clearance <= 0.0 {
        if DIAGNOSTICS {
            stats.exit = RayExit::InvalidCamera as u32;
            unsafe { *diagnostics.add(idx) = stats };
        }
        unsafe { *out_image.add(idx) = vec4(0.0, 0.0, 0.0, 1.0) };
        return;
    }
    let mut ray = init_ray(cam.pos, dir, metric, cam);
    let mut rgb = vec3_splat(0.0);
    let mut stokes = vec4_splat(0.0);
    let mut transmission = 1.0_f32;
    let mut foreground = faraday_rotation(vec3_splat(0.0), 0.0);
    let mut iterations = 0u32;
    let mut affine = 0.0_f32;
    let mut next_h = 1.0e8_f32;
    let mut capture_clearance = if early_capture && supports_early_capture(objects, disk) {
        EARLY_CAPTURE_CLEARANCE
    } else {
        0.0
    };
    let vacuum_sq = if far_field { vacuum_radius_sq(objects, disk) } else { f32::INFINITY };
    // Coordinate time relative to the camera; it decreases along the backward ray.
    let mut ray_time = 0.0_f32;
    let mut winding = 0.0_f32;
    let mut i = 0u32;
    while i < cam.max_iter {
        iterations = i + 1;
        if metric.clearance < 0.002 || !metric.valid {
            if DIAGNOSTICS {
                exit = if !metric.valid {
                    RayExit::InvalidMetric
                } else if winding > UNRESOLVED_WINDING {
                    RayExit::NearCritical
                } else {
                    RayExit::Horizon
                };
            }
            break;
        }
        let velocity = (metric.inv * ray.p).yzw();
        let start_dt = if SWARM { (metric.inv * ray.p).x } else { 0.0 };
        if early_capture && metric.clearance < capture_clearance {
            // A tighter interval may rule out a turn even if the first check could not.
            capture_clearance = 0.5 * metric.clearance;
            if inward_kerr_capture(ray, velocity, disk.spin, disk.r1) {
                if DIAGNOSTICS {
                    exit = if winding > UNRESOLVED_WINDING {
                        RayExit::NearCritical
                    } else {
                        RayExit::EarlyCapture
                    };
                }
                break;
            }
        }
        let mut distance = clamp_f32(0.12 * metric.clearance, 0.0002, 32.0);
        let clearance_limited_distance = distance;
        let radius = disk_radius(ray.pos, disk.spin, disk.binary_enabled != 0);
        // Decoupled transfer: the length of the constant cells this step's plasma is
        // split into, or zero for one midpoint cell.
        let mut cell_length = 0.0_f32;
        if radius > disk.r1 - distance && radius < disk.r2 + distance {
            let r_clamped = radius.max(disk.r1);
            let height_d = (get_h_over_r(r_clamped, disk) * r_clamped).max(0.001);
            let mid = disk_midplane_y(radius.max(0.001), ray.pos.xz(), disk);
            let to_disk = ((ray.pos.y - mid).abs() - 4.0 * height_d).max(0.0);
            let refinement = 1.0 / (1u32 << refine) as f32;
            let cell = 0.25 * height_d * refinement;
            if !decoupled {
                distance = distance.min(cell.max(0.5 * to_disk));
            } else if 0.5 * to_disk < distance {
                // The coupled scheme's margin: a chord shorter than half the vertical
                // distance `to_disk` does not reach the emitting slab, tilted or not.
                let length = cell.min(ORBIT_CELL * r_clamped * refinement);
                distance = distance.min((MAX_TRANSFER_CELLS as f32 * length).max(0.5 * to_disk));
                if distance > 0.5 * to_disk {
                    cell_length = length;
                }
            }
        }
        let near_horizon = DIAGNOSTICS && metric.clearance < 1.0;
        let speed = velocity.length().max(1.0e-6);
        let geometric_h = distance / speed;
        let ordinary_h = geometric_h.min(next_h);
        let proposed_h = if far_field {
            let far_distance = far_field_distance(ray.pos, velocity, speed, vacuum_sq);
            ordinary_h.max((far_distance / speed).min(next_h))
        } else {
            ordinary_h
        };
        let mut step = advance_render_ray::<DIAGNOSTICS, PATH>(ray, proposed_h, &mut metric, objects, &mut stats, dormand_prince);
        if far_field && proposed_h > ordinary_h
            && (!step.accepted || ray.pos.dot(step.ray.pos - ray.pos) < 0.0)
        {
            // An outward chord stays outside the sphere, including its transfer midpoint.
            if step.accepted {
                metric = scene_metric(ray.pos, objects);
            }
            step = advance_render_ray::<DIAGNOSTICS, PATH>(ray, ordinary_h, &mut metric, objects, &mut stats, dormand_prince);
        }
        // Stop when the affine parameter can no longer advance in binary32.
        if !step.accepted || affine + step.h == affine {
            if DIAGNOSTICS {
                exit = if step.accepted { RayExit::AffineStagnation } else { RayExit::StepRejected };
            }
            break;
        }
        let disk_limited = DIAGNOSTICS && geometric_h <= next_h
            && distance < clearance_limited_distance && step.h <= ordinary_h;
        if DIAGNOSTICS {
            stats.steps += 1;
            stats.near_horizon_steps += near_horizon as u32;
            stats.far_field_steps += (ray.pos.dot(ray.pos) >= 64.0 * 64.0) as u32;
            stats.disk_limited_steps += disk_limited as u32;
            stats.controller_limited_steps += (next_h < geometric_h) as u32;
            stats.wide_steps += (step.h > ordinary_h) as u32;
        }
        affine += step.h;
        let h = step.h;
        let next = step.ray;
        next_h = h * clamp_f32(0.9 * pow(STEP_TOLERANCE / step.error.max(1.0e-20), 0.2), 0.5, 2.0);
        let hit = intersect_objects_segment(ray.pos, next.pos, objects);
        if hit.hit {
            let intensity = hit.color.xyz().dot(vec3(0.2126, 0.7152, 0.0722));
            rgb += transmission * hit.color.xyz();
            stokes.x += transmission * intensity;
            if DIAGNOSTICS {
                exit = RayExit::ObjectHit;
            }
            break;
        }
        if SWARM {
            // Trapezoidal dt/dλ; `metric` now holds the accepted endpoint's metric.
            let end_time = ray_time + 0.5 * h * (start_dt + (metric.inv * next.p).x);
            let state = PixelState { rgb, transmission, stokes, iterations };
            let body = swarm_hit(ray.pos, next.pos, ray_time, end_time, state);
            ray_time = end_time;
            if body.w > 0.0 {
                rgb += transmission * body.xyz();
                stokes.x += transmission * body.xyz().dot(vec3(0.2126, 0.7152, 0.0722));
                if DIAGNOSTICS {
                    exit = RayExit::ObjectHit;
                }
                break;
            }
        }
        let cells = if cell_length > 0.0 {
            clamp_f32(-floor_f32(-h * speed / cell_length), 1.0, MAX_TRANSFER_CELLS as f32) as u32
        } else {
            1
        };
        let mut sampled = false;
        let mut cell = 0u32;
        while cell < cells {
            let middle = if decoupled {
                hermite_ray(ray, next, step.rates, h, (cell as f32 + 0.5) / cells as f32)
            } else {
                Ray {
                    pos: 0.5 * (ray.pos + next.pos),
                    p: 0.5 * (ray.p + next.p),
                    screen: 0.5 * (ray.screen + next.screen),
                }
            };
            let plasma = sample_plasma(middle, objects, cam, disk);
            let ds = h / cells as f32 * plasma.energy;
            if ds > 0.0 {
                sampled = true;
                composite_plasma(
                    &plasma,
                    ds,
                    cam.polarization_view != 0,
                    &mut rgb,
                    &mut stokes,
                    &mut transmission,
                    &mut foreground,
                );
            }
            cell += 1;
        }
        if DIAGNOSTICS {
            stats.plasma_steps += sampled as u32;
            stats.vacuum_disk_steps += (disk_limited && !sampled) as u32;
        }
        winding += swept_angle(ray.pos, next.pos);
        ray = next;
        if PATH != SINGLE_SCALAR {
            let frame = screen_frame(ray, metric);
            ray.screen = vec4_f_v3(0.0, frame[0]);
        }
        if ray.pos.length() > ESCAPE_R && winding > UNRESOLVED_WINDING {
            // Unresolved: no sky, as for the iteration limit; captures already add none.
            if DIAGNOSTICS {
                exit = RayExit::NearCritical;
            }
            break;
        }
        if ray.pos.length() > ESCAPE_R {
            let direction = (metric.inv * ray.p).yzw().normalize();
            let sky = unsafe {
                sample_skybox(
                    direction,
                    skybox,
                    sky_w as i32,
                    sky_h as i32,
                )
            };
            rgb += transmission * sky;
            stokes.x += transmission * sky.dot(vec3(0.2126, 0.7152, 0.0722));
            if DIAGNOSTICS {
                exit = RayExit::Escaped;
                stats.sky_direction = [direction.x, direction.y, direction.z];
            }
            break;
        }
        if transmission < 0.001 {
            if DIAGNOSTICS {
                exit = RayExit::Opaque;
            }
            break;
        }
        i += 1;
    }
    let output = pixel_output(rgb, stokes, iterations, cam);
    if DIAGNOSTICS {
        stats.iterations = iterations;
        stats.exit = exit as u32;
        stats.stokes = [stokes.x, stokes.y, stokes.z, stokes.w];
        unsafe { *diagnostics.add(idx) = stats };
    }
    unsafe {
        *out_image.add(idx) = vec4_v3_f(output, 1.0);
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_accumulate(
    display: *mut u32,
    new_frame: *const Vec4,
    prev_accum: *const Vec4,
    curr_accum: *mut Vec4,
    width: u32,
    height: u32,
    frame_count: u32,
) {
    let pix_x = gid_x();
    let pix_y = gid_y();
    if pix_x >= width || pix_y >= height {
        return;
    }
    let idx = (pix_y * width + pix_x) as usize;
    let new_c = unsafe { *new_frame.add(idx) };
    let out = if frame_count == 0 {
        new_c
    } else {
        let prev = unsafe { *prev_accum.add(idx) };
        prev.mix(new_c, 0.1)
    };
    unsafe {
        *curr_accum.add(idx) = out;
        *display.add(idx) = pack_rgba8(out);
    }
}

// -- GPU Physics & Numerical Verification Kernels ----------------------------

#[inline(always)]
fn matrix_error(a: Mat4, b: Mat4) -> f32 {
    let mut error = 0.0_f32;
    let mut i = 0u32;
    while i < 4 {
        let d = (a[i] - b[i]).abs();
        error = error.max(d.x.max(d.y).max(d.z.max(d.w)));
        i += 1;
    }
    error
}

#[inline(always)]
fn norm4(v: Vec4) -> f32 {
    v.x.abs().max(v.y.abs()).max(v.z.abs().max(v.w.abs()))
}

#[inline(always)]
fn verification_metric(pos: Vec3, binary: bool) -> MetricJet {
    let flat = MetricJet { m: flat_metric(), ..MetricJet::default() };
    if binary {
        return add_kerr_jet(
            add_kerr_jet(
                flat,
                pos + vec3(7.0, 0.0, 0.0),
                0.5,
                vec3_splat(0.0),
            ),
            pos - vec3(7.0, 0.0, 0.0),
            0.5,
            vec3_splat(0.0),
        );
    }
    add_kerr_jet(
        flat,
        pos + vec3(7.0, 0.0, 0.0),
        1.0,
        vec3_splat(0.0),
    )
}

#[inline(always)]
fn metric_derivative(m: MetricJet, i: u32) -> Mat4 {
    if i == 1 {
        return m.dx;
    }
    if i == 2 {
        return m.dy;
    }
    if i == 3 {
        return m.dz;
    }
    Mat4::default()
}

#[inline(always)]
fn connection(m: MetricJet, a: u32, b: u32, c: u32) -> f32 {
    let db = metric_derivative(m, b);
    let dc = metric_derivative(m, c);
    let mut value = 0.0_f32;
    let mut d = 0u32;
    while d < 4 {
        let dd = metric_derivative(m, d);
        value += 0.5 * m.m.inv[d][a] * (db[c][d] + dc[b][d] - dd[c][b]);
        d += 1;
    }
    value
}

#[cuda_device::device]
fn vacuum_ricci_tt(binary: bool, epsilon: f32) -> f32 {
    let m = verification_metric(vec3_splat(0.0), binary);
    let mut result = 0.0_f32;
    let mut a = 0u32;
    while a < 4 {
        if a > 0 {
            let mut delta = vec3_splat(0.0);
            delta[a - 1] = epsilon;
            let plus = verification_metric(delta, binary);
            let minus = verification_metric(-delta, binary);
            result += (connection(plus, a, 0, 0) - connection(minus, a, 0, 0)) / (2.0 * epsilon);
        }
        let mut b = 0u32;
        while b < 4 {
            result += connection(m, a, a, b) * connection(m, b, 0, 0)
                - connection(m, a, 0, b) * connection(m, b, 0, a);
            b += 1;
        }
        a += 1;
    }
    result
}

#[cuda_device::device]
unsafe fn convergence_sample(sample: u32, cam: &Camera, objects: &Objects, checks: *mut f32) {
    let pos = vec3(6.0, 0.0, 20.0);
    let mut metric = scene_metric(pos, objects);
    let mut ray = init_ray(pos, vec3(0.0, 0.0, -1.0), metric, cam);
    if sample > 0 {
        let steps = 10u32 << (sample - 1);
        let h = 40.0 / steps as f32;
        let mut i = 0u32;
        while i < steps {
            let step = step_ray(ray, h, metric, objects);
            if !step.valid {
                unsafe { *checks.add((40 + 12 * sample + 3) as usize) = -1.0 };
                return;
            }
            ray = step.ray;
            metric = scene_metric(ray.pos, objects);
            ray.screen = vec4_f_v3(0.0, screen_frame(ray, metric)[0]);
            i += 1;
        }
    }
    let base = (40 + 12 * sample) as usize;
    unsafe {
        *checks.add(base + 3) = 1.0;
        let k = (metric.inv * ray.p).yzw();
        let mut i = 0u32;
        while i < 3 {
            *checks.add(base + i as usize) = ray.pos[i];
            *checks.add(base + 8 + i as usize) = k[i];
            i += 1;
        }
        let mut j = 0u32;
        while j < 4 {
            *checks.add(base + 4 + j as usize) = ray.p[j];
            j += 1;
        }
        *checks.add(base + 11) = ray.p.dot(metric.inv * ray.p).abs() / ray.p.dot(ray.p);
    }
}

#[cuda_device::device]
fn trajectory(impact: f32, cam: &Camera, objects: &Objects) -> Vec4 {
    let mut metric = scene_metric(vec3(impact, 0.0, 100.0), objects);
    let mut ray = init_ray(vec3(impact, 0.0, 100.0), vec3(0.0, 0.0, -1.0), metric, cam);
    let energy = ray.p.x;
    let mut error = 0.0_f32;
    let mut screen_error = 0.0_f32;
    let mut i = 0u32;
    while i < 3000 {
        if metric.clearance < 0.002 {
            return vec4(1.0, error, screen_error, (ray.p.x - energy).abs());
        }
        let h = clamp_f32(0.08 * metric.clearance, 0.0001, 2.0)
            / (metric.inv * ray.p).yzw().length();
        let step = advance_ray(ray, h, metric, objects);
        if !step.accepted {
            return vec4(-1.0, error, screen_error, 1.0);
        }
        ray = step.ray;
        metric = scene_metric(ray.pos, objects);
        error = error.max(ray.p.dot(metric.inv * ray.p).abs() / ray.p.dot(ray.p));
        screen_error = screen_error.max((ray.screen.dot(metric.g * ray.screen) - 1.0).abs());
        screen_error = screen_error.max(ray.p.dot(ray.screen).abs() / ray.p.length());
        ray.screen = vec4_f_v3(0.0, screen_frame(ray, metric)[0]);
        if ray.pos.length() > 110.0 {
            return vec4(0.0, error, screen_error, (ray.p.x - energy).abs());
        }
        i += 1;
    }
    vec4(-1.0, error, screen_error, 1.0)
}

#[cuda_device::kernel]
pub unsafe fn bh_check_relativity(
    cam: *const Camera,
    objects: *const Objects,
    checks: *mut f32,
) {
    let i = gid_x();
    if i >= 36 {
        return;
    }
    let cam = unsafe { &*cam };
    let objects = unsafe { &*objects };
    if i >= 29 {
        let pos = vec3(4.0, 0.0, 0.0);
        let metric = scene_metric(pos, objects);
        let radial = Ray {
            pos,
            p: vec4(1.0, -3.0, 0.0, 0.0),
            screen: vec4(0.0, 0.0, 1.0, 0.0),
        };
        let mut passed = false;
        if i == 29 {
            let coarse = step_ray(radial, 0.24, metric, objects);
            let exact_r = 4.0 - 0.24;
            let residual = coarse
                .ray
                .p
                .dot(scene_metric(coarse.ray.pos, objects).inv * coarse.ray.p)
                .abs()
                / coarse.ray.p.dot(coarse.ray.p);
            let refined = advance_ray(radial, 0.24, metric, objects);
            let expected_r = 4.0 - refined.h;
            let expected_p = -(expected_r + 2.0) / (expected_r - 2.0);
            passed = coarse.valid
                && residual < 2.0e-4
                && (coarse.ray.pos.x - exact_r).abs() > 1.0e-6 * exact_r
                && refined.accepted
                && refined.h < 0.24
                && refined.error <= STEP_TOLERANCE
                && (refined.ray.pos.x - expected_r).abs() < 1.0e-6 * expected_r
                && (refined.ray.p.y - expected_p).abs() < 1.0e-6 * expected_p.abs();
        }
        if i == 30 {
            passed = !step_ray(radial, 4.0, metric, objects).valid;
        }
        if i == 31 {
            passed = !advance_ray(radial, 0.0, metric, objects).accepted
                && !advance_ray(radial, -1.0, metric, objects).accepted;
        }
        if i == 32 {
            let mut bad = radial;
            bad.screen.x = 1.0e30;
            passed = !advance_ray(bad, 0.24, metric, objects).accepted;
        }
        if i == 33 {
            let mut unchanged = true;
            let mut ray = radial;
            let mut remaining = 0.5_f32;
            let mut n = 0u32;
            while n < 100 && remaining > 1.0e-7 {
                let step = advance_ray(
                    ray,
                    remaining.min(0.24),
                    scene_metric(ray.pos, objects),
                    objects,
                );
                if !step.accepted {
                    unchanged = false;
                    break;
                }
                remaining -= step.h;
                ray = step.ray;
                n += 1;
            }
            let exact_r = 3.5 + remaining;
            let exact_p = -(exact_r + 2.0) / (exact_r - 2.0);
            passed = unchanged
                && remaining < 1.0e-7
                && (ray.pos.x - exact_r).abs() < 1.0e-6 * exact_r
                && (ray.p.y - exact_p).abs() < 1.0e-6 * expected_abs(exact_p)
                && ray.p.x == radial.p.x;
        }
        if i == 34 {
            let start = init_ray(
                vec3(6.0, 0.0, 20.0),
                vec3(0.0, 0.0, -1.0),
                scene_metric(vec3(6.0, 0.0, 20.0), objects),
                cam,
            );
            let mut ray = start;
            let mut elapsed = 0.0_f32;
            let mut valid = true;
            let mut max_screen_error = 0.0_f32;
            let mut n = 0u32;
            while n < 4000 && elapsed < 40.0 {
                let metric = scene_metric(ray.pos, objects);
                let step = advance_ray(ray, (40.0 - elapsed).min(1.0), metric, objects);
                if !step.accepted || elapsed + step.h == elapsed {
                    valid = false;
                    break;
                }
                ray = step.ray;
                elapsed += step.h;
                let m = scene_metric(ray.pos, objects);
                max_screen_error =
                    max_screen_error.max((ray.screen.dot(m.g * ray.screen) - 1.0).abs());
                max_screen_error =
                    max_screen_error.max(ray.p.dot(ray.screen).abs() / ray.p.length());
                ray.screen = vec4_f_v3(0.0, screen_frame(ray, m)[0]);
                n += 1;
            }
            let m = scene_metric(ray.pos, objects);
            let base = 112usize;
            let k = (m.inv * ray.p).yzw();
            unsafe {
                let mut j = 0u32;
                while j < 3 {
                    *checks.add(base + j as usize) = ray.pos[j];
                    *checks.add(base + 8 + j as usize) = k[j];
                    j += 1;
                }
                let mut j = 0u32;
                while j < 4 {
                    *checks.add(base + 4 + j as usize) = ray.p[j];
                    j += 1;
                }
                *checks.add(base + 3) = max_screen_error;
                *checks.add(base + 11) = elapsed;
            }
            passed = valid && elapsed == 40.0;
        }
        if i == 35 {
            let mut intensity_cam = *cam;
            intensity_cam.polarization_view = 0;
            intensity_cam.frequency_ghz = 230.0;
            let mut polarized_cam = intensity_cam;
            polarized_cam.polarization_view = 1;
            let mut disk = Disk {
                r1: 6.0, r2: 30.0, h_thin: 0.03, h_hot: 0.5,
                spin: 0.3, horizon_r: 2.0, isco_r: 6.0, r_trunc: 20.0,
                tilt_deg: 30.0, r_bp: 6.0, twist_deg: 15.0,
                model: 0, binary_enabled: 0, _pad0: 0.0, _pad1: 0.0, _pad2: 0.0,
            };
            passed = true;
            while disk.model < 4 {
                let mut pos = vec3(12.0, 0.0, 2.0);
                let r = disk_radius(pos, disk.spin, false);
                pos.y = disk_midplane_y(r, pos.xz(), &disk)
                    + 0.1 * get_h_over_r(r, &disk) * r;
                let ray = init_ray(pos, vec3(0.0, -1.0, 0.0),
                    scene_metric(pos, objects), &intensity_cam);
                let fast = sample_plasma(ray, objects, &intensity_cam, &disk);
                let full = sample_plasma(ray, objects, &polarized_cam, &disk);
                passed = passed && fast.energy == full.energy && fast.alpha == full.alpha
                    && full.rgb.length() > 0.0
                    && (fast.rgb - full.rgb).length() <= 1.0e-6 * full.rgb.length().max(1.0);
                disk.model += 1;
            }
        }
        unsafe { *checks.add((100 + i - 29) as usize) = if passed { 1.0 } else { 0.0 } };
        return;
    }
    if i >= 24 {
        unsafe { convergence_sample(i - 24, cam, objects, checks) };
        return;
    }
    let mut passed = false;
    let identity = ETA * ETA;
    let x = vec3(3.0, 2.0, 4.0);
    let spin = vec3(0.4, -0.5, 0.6);
    let jet = add_kerr_jet(MetricJet { m: flat_metric(), ..MetricJet::default() }, x, 0.7, spin);
    let m = jet.m;
    let j = vec4(1.0, 0.7, 0.1, 0.05);
    if i == 0 {
        passed = matrix_error(flat_metric().g, ETA) == 0.0;
    }
    if i == 1 {
        let s = add_kerr(flat_metric(), vec3(10.0, 0.0, 0.0), 1.0, vec3_splat(0.0));
        passed = (s.g[0][0] + 0.8).abs() < 1.0e-6 && (s.g[0][1] - 0.2).abs() < 1.0e-6;
    }
    if i == 2 {
        passed = matrix_error(m.g * m.inv, identity) < 2.0e-6;
    }
    if i == 3 {
        let b = add_kerr(m, x + vec3(8.0, 0.0, 0.0), 0.5, -spin);
        let reversed = add_kerr(
            add_kerr(flat_metric(), x + vec3(8.0, 0.0, 0.0), 0.5, -spin),
            x,
            0.7,
            spin,
        );
        passed = b.valid
            && matrix_error(b.g * b.inv, identity) < 2.0e-6
            && matrix_error(b.inv, reversed.inv) < 2.0e-6;
    }
    if i >= 4 && i <= 6 {
        let mut delta = vec3_splat(0.0);
        delta[i - 4] = 0.002;
        let plus = add_kerr(flat_metric(), x + delta, 0.7, spin);
        let minus = add_kerr(flat_metric(), x - delta, 0.7, spin);
        let mut analytic = jet.dx;
        if i == 5 {
            analytic = jet.dy;
        }
        if i == 6 {
            analytic = jet.dz;
        }
        passed = matrix_error((plus.g - minus.g) * 250.0, analytic) < 6.0e-5;
    }
    if i == 7 {
        let pro = add_kerr(
            flat_metric(),
            vec3(10.0, 0.0, 0.0),
            1.0,
            vec3(0.0, 0.0, 0.8),
        );
        let retro = add_kerr(
            flat_metric(),
            vec3(10.0, 0.0, 0.0),
            1.0,
            vec3(0.0, 0.0, -0.8),
        );
        passed = pro.g[0][2] < 0.0 && (pro.g[0][2] + retro.g[0][2]).abs() < 1.0e-7;
    }
    if i == 8 {
        let ray = init_ray(x, vec3(-1.0, 0.2, -1.0).normalize(), m, cam);
        passed = ray.p.dot(m.inv * ray.p).abs() < 2.0e-6
            && (m.inv * ray.p).x < 0.0
            && ray.p.dot(ray.screen).abs() < 2.0e-6
            && (ray.screen.dot(m.g * ray.screen) - 1.0).abs() < 2.0e-6;
    }
    if i == 9 {
        passed = norm4(polarized_cell(j, 0.0, vec3_splat(0.0), 2.0) - 2.0 * j) < 1.0e-6;
    }
    if i == 10 {
        passed = norm4(
            polarized_cell(j, 2.0, vec3_splat(0.0), 3.0) - j * ((1.0 - exp(-6.0)) / 2.0),
        ) < 1.0e-6;
    }
    if i == 11 {
        let rotated = faraday_rotation(vec3(0.0, 0.0, 1.0), PI * 0.5) * vec3(1.0, 0.0, 0.0);
        passed = (rotated - vec3(0.0, 1.0, 0.0)).length() < 1.0e-6;
    }
    if i == 12 {
        let converted = faraday_rotation(vec3(1.0, 0.0, 0.0), PI * 0.5) * vec3(0.0, 1.0, 0.0);
        passed = (converted - vec3(0.0, 0.0, 1.0)).length() < 1.0e-6;
    }
    if i == 13 {
        let cell = polarized_cell(vec4(1.0, 1.0, 0.0, 0.0), 0.0, vec3(0.0, 0.0, 1.0), PI * 0.5);
        passed = norm4(cell - vec4(PI * 0.5, 1.0, 1.0, 0.0)) < 1.0e-6;
    }
    if i == 14 {
        let rho = vec3(2.0, 3.0, 5.0);
        let whole = polarized_cell(j, 0.7, rho, 2.0);
        let half = polarized_cell(j, 0.7, rho, 1.0);
        let composed =
            half + exp(-0.7) * vec4_f_v3(half.x, faraday_rotation(rho, 1.0) * half.yzw());
        passed = norm4(whole - composed) < 2.0e-6;
    }
    if i == 15 {
        let cell = polarized_cell(j, 3.0, vec3(1000.0, 300.0, -800.0), 20.0);
        let source = vec4_f_v2_f(1.0, 0.75 * projected_evpa(2.0, 0.0), 0.0);
        let projected = polarized_cell(source, 0.7, vec3(2.0, 3.0, 5.0), 2.0);
        let gamma = spatial_metric(flat_metric());
        let tiny = spatial_unit(vec3(1.0e-12, 0.0, 0.0), gamma);
        let huge = spatial_unit(vec3(1.0e20, 0.0, 0.0), gamma);
        let zero = spatial_unit(vec3_splat(0.0), gamma);
        passed = cell.abs().all_lt(100.0)
            && cell.x >= cell.yzw().length()
            && source.x >= source.yzw().length()
            && projected.x >= projected.yzw().length()
            && (tiny.dot(gamma * tiny) - 1.0).abs() < 1.0e-6
            && (huge.dot(gamma * huge) - 1.0).abs() < 1.0e-6
            && zero == vec3_splat(0.0);
    }
    if i == 16 || i == 17 {
        let impact = if i == 17 { 5.6 } else { 4.8 };
        let ray = trajectory(impact, cam, objects);
        let mut c = 0u32;
        while c < 4 {
            unsafe { *checks.add((24 + 4 * (i - 16) + c) as usize) = ray[c] };
            c += 1;
        }
        let expected_x = if i == 17 { 0.0 } else { 1.0 };
        passed = ray.x == expected_x && ray.y < 2.0e-4 && ray.z < 0.002 && ray.w < 1.0e-7;
    }
    if i == 18 {
        let front = faraday_rotation(vec3(0.0, 0.0, 1.0), PI * 0.5);
        let back = faraday_rotation(vec3(1.0, 0.0, 0.0), PI * 0.5);
        passed = (front * (back * vec3(0.0, 1.0, 0.0)) - vec3(0.0, 0.0, 1.0)).length() < 1.0e-6;
    }
    if i == 19 {
        let r = sqrt(1.6 * 1.6 + 0.8 * 0.8);
        let pos = vec3(r, 0.0, 0.0);
        passed = (disk_radius(pos, 0.8, false) - 1.6).abs() < 1.0e-6
            && (disk_radius(pos, -0.8, false) - 1.6).abs() < 1.0e-6
            && (disk_radius(pos, 0.8, true) - r).abs() < 1.0e-6
            && (disk_radius(pos + vec3(0.0, 7.0, 0.0), 0.8, false) - 1.6).abs() < 1.0e-6
            && disk_radius(vec3(0.0, 10.0, 0.0), 0.8, false) < 0.001;
    }
    if i == 20 {
        passed =
            (kerr_radius(vec3(0.0, 0.0, 0.0001), vec3(0.0, 0.0, 0.8)) - 0.0001).abs() < 1.0e-8;
    }
    if i == 21 {
        let first = init_ray(x, vec3(0.0, 0.0, -1.0), flat_metric(), cam);
        let second = init_ray(x, vec3(1.0, 0.0, 0.0), flat_metric(), cam);
        passed = first.p.dot(ETA * first.p) == 0.0
            && second.p.dot(ETA * second.p) == 0.0
            && first.p.x == second.p.x
            && (first.p - second.p).length() > 1.0;
    }
    if i == 22 || i == 23 {
        let binary = i == 23;
        let coarse = vacuum_ricci_tt(binary, 0.02);
        let fine = vacuum_ricci_tt(binary, 0.01);
        unsafe {
            *checks.add((32 + 2 * (i - 22)) as usize) = coarse;
            *checks.add((33 + 2 * (i - 22)) as usize) = fine;
        }
        let expected = if binary { 4.0 / 3087.0 } else { 0.0 };
        passed = (coarse - expected).abs() < 2.0e-6 && (fine - expected).abs() < 2.0e-6;
    }
    unsafe { *checks.add(i as usize) = if passed { 1.0 } else { 0.0 } };
}

#[inline(always)]
fn expected_abs(x: f32) -> f32 {
    x.abs()
}

// -- Standalone Test Kernels -------------------------------------------------

#[cuda_device::kernel]
pub unsafe fn bh_test_atan2(points: *const Vec2, values: *mut f32, count: u32) {
    let i = gid_x();
    if i >= count {
        return;
    }
    let pt = unsafe { *points.add(i as usize) };
    unsafe {
        *values.add(i as usize) = atan2_arith(pt.x, pt.y);
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_sincos(angles: *const f32, values: *mut Vec2, count: u32) {
    let i = gid_x();
    if i >= count {
        return;
    }
    let a = unsafe { *angles.add(i as usize) };
    unsafe {
        *values.add(i as usize) = sincos(a);
    }
}

#[inline(always)]
unsafe fn read_matrix(inputs: *const f32, base: usize) -> Mat4 {
    let mut m = Mat4::default();
    let mut c = 0u32;
    while c < 4 {
        let mut r = 0u32;
        while r < 4 {
            m[c][r] = unsafe { *inputs.add(base + (4 * r + c) as usize) };
            r += 1;
        }
        c += 1;
    }
    m
}

#[inline(always)]
unsafe fn read_vec4(inputs: *const f32, base: usize) -> Vec4 {
    unsafe {
        vec4(
            *inputs.add(base),
            *inputs.add(base + 1),
            *inputs.add(base + 2),
            *inputs.add(base + 3),
        )
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_geodesic_rhs(inputs: *const f32, values: *mut f32, count: u32) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let b = (id * 72) as usize;
    let mut m = MetricJet::default();
    unsafe {
        m.m.inv = read_matrix(inputs, b);
        m.dx = read_matrix(inputs, b + 16);
        m.dy = read_matrix(inputs, b + 32);
        m.dz = read_matrix(inputs, b + 48);
        let d = geodesic_rhs_matrix(
            Ray {
                pos: vec3_splat(0.0),
                p: read_vec4(inputs, b + 64),
                screen: read_vec4(inputs, b + 68),
            },
            m,
        );
        let o = (id * 11) as usize;
        *values.add(o) = d.pos.x;
        *values.add(o + 1) = d.pos.y;
        *values.add(o + 2) = d.pos.z;
        let mut i = 0u32;
        while i < 4 {
            *values.add(o + 3 + i as usize) = d.p[i];
            *values.add(o + 7 + i as usize) = d.screen[i];
            i += 1;
        }
    }
}

/// Per state (pos, p, screen at stride 12): the matrix reference, the structured
/// `geodesic_rhs` and the fused `metric_and_rhs`, 11 values each, then 1 when the fused
/// metric has `scene_metric`'s bits (0 if not, -1 if the ray is invalid there).
#[cuda_device::kernel]
pub unsafe fn bh_test_rhs_forms(objects: *const Objects, inputs: *const f32, values: *mut f32, count: u32) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let objects = unsafe { &*objects };
    let b = (id * 12) as usize;
    unsafe {
        let ray = Ray {
            pos: read_vec4(inputs, b).xyz(),
            p: read_vec4(inputs, b + 4),
            screen: read_vec4(inputs, b + 8),
        };
        let mut jet = MetricJet { m: flat_metric(), ..MetricJet::default() };
        let mut i = 0i32;
        while i < objects.num_objects {
            let idx = i as usize;
            let x = ray.pos - objects.pos_radius[idx].xyz();
            jet = add_kerr_jet(jet, x, objects.mass[idx].x.max(0.0), objects.spin[idx].xyz());
            i += 1;
        }
        let m = scene_metric(ray.pos, objects);
        let (fused_m, fused) = metric_and_rhs(ray, false, objects);
        let o = (id * 34) as usize;
        let forms = [
            geodesic_rhs_matrix(ray, jet),
            geodesic_rhs(ray, m, objects),
            fused.unwrap_or_default(),
        ];
        let mut f = 0usize;
        while f < 3 {
            let d = forms[f];
            let base = o + 11 * f;
            let mut j = 0u32;
            while j < 4 {
                if j < 3 {
                    *values.add(base + j as usize) = d.pos[j];
                }
                *values.add(base + 3 + j as usize) = d.p[j];
                *values.add(base + 7 + j as usize) = d.screen[j];
                j += 1;
            }
            f += 1;
        }
        let mut same = true;
        let mut r = 0u32;
        while r < 4 {
            let mut c = 0u32;
            while c < 4 {
                same = same
                    && fused_m.g[r][c].to_bits() == m.g[r][c].to_bits()
                    && fused_m.inv[r][c].to_bits() == m.inv[r][c].to_bits();
                c += 1;
            }
            r += 1;
        }
        same = same && fused_m.clearance.to_bits() == m.clearance.to_bits() && fused_m.valid == m.valid;
        *values.add(o + 33) = if fused.is_none() { -1.0 } else if same { 1.0 } else { 0.0 };
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_energy(
    cam: *const Camera,
    disk: *const Disk,
    objects: *const Objects,
    extremes: *mut Vec4,
) {
    let n = 32u32;
    let gx = gid_x();
    let gy = gid_y();
    if gx >= n || gy >= n {
        return;
    }
    let cam = unsafe { &*cam };
    let disk = unsafe { &*disk };
    let objects = unsafe { &*objects };
    let u = (2.0 * (gx as f32 + 0.5) / n as f32 - 1.0) * cam.aspect * cam.tan_half_fov;
    let v = (1.0 - 2.0 * (gy as f32 + 0.5) / n as f32) * cam.tan_half_fov;
    let dir = (u * cam.right - v * cam.up + cam.forward).normalize();
    let mut metric = scene_metric(cam.pos, objects);
    let mut low = 1.0e30_f32;
    let mut high = -1.0e30_f32;
    let mut samples = 0.0_f32;
    if metric.valid && metric.clearance > 0.0 {
        let mut ray = init_ray(cam.pos, dir, metric, cam);
        let mut next_h = 1.0e8_f32;
        let mut i = 0u32;
        while i < cam.max_iter {
            if metric.clearance < 0.002 || !metric.valid {
                break;
            }
            let velocity = (metric.inv * ray.p).yzw();
            let mut distance = clamp_f32(0.12 * metric.clearance, 0.0002, 32.0);
            let radius = disk_radius(ray.pos, disk.spin, disk.binary_enabled != 0);
            let r_clamped = radius.max(disk.r1);
            let height = (get_h_over_r(r_clamped, disk) * r_clamped).max(0.001);
            if radius > disk.r1 - distance && radius < disk.r2 + distance {
                let mid = disk_midplane_y(radius.max(0.001), ray.pos.xz(), disk);
                let to_disk = ((ray.pos.y - mid).abs() - 4.0 * height).max(0.0);
                distance = distance.min((0.25 * height).max(0.5 * to_disk));
            }
            let step = advance_ray(
                ray,
                (distance / velocity.length().max(1.0e-6)).min(next_h),
                metric,
                objects,
            );
            if !step.accepted {
                break;
            }
            next_h = step.h
                * clamp_f32(
                    0.9 * pow(STEP_TOLERANCE / step.error.max(1.0e-20), 0.2),
                    0.5,
                    2.0,
                );
            ray = step.ray;
            metric = scene_metric(ray.pos, objects);
            ray.screen = vec4_f_v3(0.0, screen_frame(ray, metric)[0]);
            let plasma = sample_plasma(ray, objects, cam, disk);
            if plasma.alpha > 0.0 {
                low = low.min(plasma.energy);
                high = high.max(plasma.energy);
                samples += 1.0;
            }
            if ray.pos.length() > ESCAPE_R {
                break;
            }
            i += 1;
        }
    }
    unsafe {
        *extremes.add((gy * n + gx) as usize) = vec4(low, high, samples, 0.0);
    }
}

#[inline(always)]
fn controller_initial_ray(impact: f32, objects: &Objects) -> Ray {
    let pos = vec3(impact, 0.0, 100.0);
    let metric = scene_metric(pos, objects);
    let gamma = spatial_metric(metric);
    let n = spatial_unit(vec3(0.0, 0.0, -1.0), gamma);
    let lapse = inverse_sqrt(-metric.inv[0][0]);
    let shift = -metric.inv[0].yzw() / metric.inv[0][0];
    let k = vec4_f_v3(-1.0 / lapse, n + shift / lapse);
    let right = spatial_unit(
        vec3(1.0, 0.0, 0.0) - n * n.dot(gamma * vec3(1.0, 0.0, 0.0)),
        gamma,
    );
    Ray {
        pos,
        p: metric.g * k,
        screen: vec4_f_v3(0.0, right),
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_controller_classify(
    objects: *const Objects,
    cases: *const Vec4,
    results: *mut Vec4,
    count: u32,
) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let objects = unsafe { &*objects };
    let c = unsafe { *cases.add(id as usize) };
    let mut ray = controller_initial_ray(c.x, objects);
    let start = ray;
    let mut metric = scene_metric(ray.pos, objects);
    let mut capture_clearance = if c.y != 0.0 { EARLY_CAPTURE_CLEARANCE } else { 0.0 };
    let mut next_h = 1.0e8_f32;
    let mut status = 0.0_f32;
    let mut steps = 0u32;
    let mut winding = 0.0_f32;
    // cases.w overrides the geometric step factor, for robustness sweeps.
    let step_factor = if c.w != 0.0 { c.w } else { 0.12 };
    let mut i = 0u32;
    while i < 10000 {
        if metric.clearance < 0.002 || !metric.valid {
            status = 1.0;
            break;
        }
        let velocity = (metric.inv * ray.p).yzw();
        if metric.clearance < capture_clearance {
            capture_clearance = 0.5 * metric.clearance;
            if inward_kerr_capture(ray, velocity, objects.spin[0].y, c.y) {
                status = 4.0;
                break;
            }
        }
        let distance = clamp_f32(step_factor * metric.clearance, 0.0002, 32.0);
        let wanted = (distance / velocity.length().max(1.0e-6)).min(next_h);
        // cases.z != 0 selects the Dormand–Prince controller.
        let step = if c.z != 0.0 {
            let mut m = metric;
            advance_ray_dp45::<false, GENERIC>(ray, wanted, &mut m, false, objects, &mut 0)
        } else {
            advance_ray(ray, wanted, metric, objects)
        };
        if !step.accepted {
            status = 3.0;
            break;
        }
        next_h = step.h
            * clamp_f32(
                0.9 * pow(STEP_TOLERANCE / step.error.max(1.0e-20), 0.2),
                0.5,
                2.0,
            );
        winding += swept_angle(ray.pos, step.ray.pos);
        ray = step.ray;
        metric = scene_metric(ray.pos, objects);
        ray.screen = vec4_f_v3(0.0, screen_frame(ray, metric)[0]);
        steps += 1;
        if ray.pos.length() > ESCAPE_R {
            status = 2.0;
            break;
        }
        i += 1;
    }
    // Captured (1), escaped (2) or early capture (4) inside the band: unresolved (5).
    if (status == 1.0 || status == 2.0 || status == 4.0) && winding > UNRESOLVED_WINDING {
        status = 5.0;
    }
    let base = (4 * id) as usize;
    unsafe {
        *results.add(base) = vec4_v3_f(start.pos, status);
        *results.add(base + 1) = start.p;
        *results.add(base + 2) = vec4_v3_f(ray.pos, steps as f32);
        *results.add(base + 3) = vec4_v3_f(ray.p.yzw(), winding);
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_controller_trace(
    objects: *const Objects,
    cases: *const Vec4,
    results: *mut Vec4,
    count: u32,
) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let objects = unsafe { &*objects };
    let c = unsafe { *cases.add(id as usize) };
    let mut ray = controller_initial_ray(c.x, objects);
    let start = ray;
    let mut metric = scene_metric(ray.pos, objects);
    let mut affine = 0.0_f32;
    let mut next_h = 1.0e8_f32;
    let mut steps = 0u32;
    let mut rejected = 0u32;
    let mut status = 1.0_f32;
    let mut i = 0u32;
    while i < 200000 && affine < c.y {
        if metric.clearance < 0.002 || !metric.valid {
            status = 2.0;
            break;
        }
        let velocity = (metric.inv * ray.p).yzw();
        let distance = clamp_f32(0.12 * metric.clearance, 0.0002, 32.0);
        let wanted = (distance / velocity.length().max(1.0e-6))
            .min(next_h)
            .min(c.y - affine);
        // cases.z != 0 selects the production Dormand–Prince controller; zero the legacy RK4 one.
        let mut m = metric;
        let step = if c.z != 0.0 {
            advance_ray_dp45::<true, GENERIC>(ray, wanted, &mut m, false, objects, &mut rejected)
        } else {
            advance_ray_counting::<true>(ray, wanted, &mut m, false, objects, &mut rejected)
        };
        if !step.accepted {
            status = 3.0;
            break;
        }
        affine += step.h;
        next_h = step.h
            * clamp_f32(
                0.9 * pow(STEP_TOLERANCE / step.error.max(1.0e-20), 0.2),
                0.5,
                2.0,
            );
        ray = step.ray;
        metric = scene_metric(ray.pos, objects);
        ray.screen = vec4_f_v3(0.0, screen_frame(ray, metric)[0]);
        steps += 1;
        i += 1;
    }
    let base = (5 * id) as usize;
    unsafe {
        *results.add(base) = vec4_v3_f(start.pos, status);
        *results.add(base + 1) = start.p;
        *results.add(base + 2) = vec4_v3_f(ray.pos, affine);
        *results.add(base + 3) = vec4_v3_f(ray.p.yzw(), steps as f32);
        *results.add(base + 4) = vec4(rejected as f32, 0.0, 0.0, 0.0);
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_snapshot(
    header: *const SnapshotHeader,
    primitives0: *const Vec4,
    primitives1: *const Vec4,
    physical_grid: *const Vec4,
    positions: *const Vec4,
    samples: *mut Vec4,
    count: u32,
) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let header = unsafe { &*header };
    let pos = unsafe { (*positions.add(id as usize)).xyz() };
    let result = unsafe { sample_snapshot(pos, header, primitives0, primitives1, physical_grid) };
    let flag = if result.valid {
        if result.emitting { 1.0 } else { 0.0 }
    } else {
        -1.0
    };
    let base = (4 * id) as usize;
    unsafe {
        *samples.add(base) = result.velocity;
        *samples.add(base + 1) = result.magnetic;
        *samples.add(base + 2) = result.physical;
        *samples.add(base + 3) = vec4_v3_f(result.native, flag);
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_thermal(
    thermal_bessel: *const Vec2,
    cases: *const Vec4,
    results: *mut Vec4,
    count: u32,
) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let c0 = unsafe { *cases.add((id * 2) as usize) };
    let c1 = unsafe { *cases.add((id * 2 + 1) as usize) };
    let result = unsafe { thermal_coefficients(c0.xyz(), c1.x, c1.y, thermal_bessel) };
    let base = (id * 3) as usize;
    unsafe {
        *results.add(base) = result.coefficients.emission;
        *results.add(base + 1) = result.coefficients.absorption;
        *results.add(base + 2) = vec4_v3_f(
            result.coefficients.faraday,
            if result.valid { 1.0 } else { 0.0 },
        );
    }
}

#[cuda_device::kernel]
pub unsafe fn bh_test_transfer(cases: *const Vec4, results: *mut Vec4, count: u32) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let base_in = (id * 4) as usize;
    let c0 = unsafe { *cases.add(base_in) };
    let c1 = unsafe { *cases.add(base_in + 1) };
    let c2 = unsafe { *cases.add(base_in + 2) };
    let c3 = unsafe { *cases.add(base_in + 3) };
    let c = TransferCoefficients {
        emission: c0,
        absorption: c1,
        faraday: c2.xyz(),
    };
    let result = transfer_cell(c3, c, c2.w);
    let base_out = (id * 2) as usize;
    unsafe {
        *results.add(base_out) = result.stokes;
        *results.add(base_out + 1) = vec4(if result.valid { 1.0 } else { 0.0 }, 0.0, 0.0, 0.0);
    }
}

const TEST_PATH_CELLS: usize = 8;

/// Checklist P1.9: composites a fixed path of constant-coefficient cells, camera side
/// first, with the renderer's own cell routine. Each cell is three vectors: the Stokes
/// emissivity, (alpha, rho) and (ds, scalar emissivity, -, -).
#[cuda_device::kernel]
pub unsafe fn bh_test_transfer_path(cases: *const Vec4, results: *mut Vec4, count: u32) {
    let id = gid_x();
    if id >= count {
        return;
    }
    let mut rgb = vec3_splat(0.0);
    let mut stokes = vec4_splat(0.0);
    let mut transmission = 1.0_f32;
    let mut foreground = faraday_rotation(vec3_splat(0.0), 0.0);
    let mut cell = 0usize;
    while cell < TEST_PATH_CELLS {
        let base = id as usize * 3 * TEST_PATH_CELLS + 3 * cell;
        let (j, k, extent) = unsafe { (*cases.add(base), *cases.add(base + 1), *cases.add(base + 2)) };
        let plasma = Plasma {
            rgb: vec3_splat(extent.y),
            j,
            alpha: k.x,
            rho: k.yzw(),
            energy: 1.0,
        };
        composite_plasma(&plasma, extent.x, true, &mut rgb, &mut stokes, &mut transmission, &mut foreground);
        cell += 1;
    }
    unsafe {
        *results.add(2 * id as usize) = stokes;
        *results.add(2 * id as usize + 1) = vec4(rgb.x, transmission, 0.0, 0.0);
    }
}

#[inline(always)]
fn radius_rate(pos: Vec3, k: Vec3, r: f32) -> f32 {
    let a = vec3(0.0, 0.9375, 0.0);
    ((r * pos + (a.dot(pos) / r) * a) / (2.0 * r * r - pos.dot(pos) + a.dot(a))).dot(k)
}

#[inline(always)]
fn grid_step(
    pos: Vec3,
    k: Vec3,
    r: f32,
    dr: f32,
    header: &SnapshotHeader,
    settings_x: f32,
) -> f32 {
    let a = 0.9375_f32;
    let s = sqrt(pos.xz().dot(pos.xz()) / (r * r + a * a));
    let dtheta = -(k.y / r - pos.y * dr / (r * r)) / s.max(1.0e-8);
    let th = atan2_arith(s, pos.y / r);
    let mut lo = 0.0_f32;
    let mut hi = 1.0_f32;
    let mut i = 0u32;
    while i < 25 {
        let mid = 0.5 * (lo + hi);
        let angle = 3.141592653589793 * mid + 0.35 * sin(6.283185307179586 * mid);
        if angle < th {
            lo = mid;
        } else {
            hi = mid;
        }
        i += 1;
    }
    let x2 = 0.5 * (lo + hi);
    let dth = 3.141592653589793 * (1.0 + 0.7 * cos(6.283185307179586 * x2));
    let aa = -r * pos.z - a * pos.x;
    let bb = r * pos.x - a * pos.z;
    let da = -dr * pos.z - r * k.z - a * k.x;
    let db = dr * pos.x + r * k.x - a * k.z;
    let dphi = (bb * da - aa * db) / (aa * aa + bb * bb).max(1.0e-20);
    let rates = vec3(dr / r, dtheta / dth, dphi).abs() / header.spacing.xyz();
    settings_x / rates.x.max(rates.y).max(rates.z.max(1.0e-8))
}

#[inline(always)]
fn camera_stokes(s: Vec4, j: Vec4) -> Vec4 {
    let n11 = j.x * j.x * (s.x + s.y) + j.y * j.y * (s.x - s.y) + 2.0 * j.x * j.y * s.z;
    let n22 = j.z * j.z * (s.x + s.y) + j.w * j.w * (s.x - s.y) + 2.0 * j.z * j.w * s.z;
    let u = j.x * j.z * (s.x + s.y) + j.y * j.w * (s.x - s.y) + (j.x * j.w + j.y * j.z) * s.z;
    vec4(
        0.5 * (n11 + n22),
        -0.5 * (n11 - n22),
        -u,
        (j.x * j.w - j.y * j.z) * s.w,
    )
}

#[cuda_device::kernel]
pub unsafe fn bh_test_image(
    objects: *const Objects,
    header: *const SnapshotHeader,
    primitives0: *const Vec4,
    primitives1: *const Vec4,
    physical_grid: *const Vec4,
    thermal_bessel: *const Vec2,
    seeds: *const ImageSeed,
    settings: *const Vec4,
    pixels: *mut Vec4,
    dormand_prince: u32,
) {
    let id = gid_x();
    let settings = unsafe { *settings };
    if id >= settings.z as u32 {
        return;
    }
    let objects = unsafe { &*objects };
    let header = unsafe { &*header };
    let seed = unsafe { *seeds.add(id as usize) };
    let mut ray = Ray {
        pos: seed.position.xyz(),
        p: seed.momentum,
        screen: seed.screen,
    };
    let mut foreground = IDENTITY4;
    let mut intensity = vec4_splat(0.0);
    let mut next_h = 500.0_f32;
    let mut affine = seed.position.w;
    let mut max_null = 0.0_f32;
    let mut status = 3u32;
    let mut steps = 0u32;
    let mut last_h = 0.0_f32;
    let mut last_actual = 0.0_f32;
    let mut last_error = 0.0_f32;
    let sin_00174 = 0.017_399_122_f32;
    let max_iterations = settings.y as u32;
    let mut iteration = 0u32;
    while iteration < max_iterations {
        steps = iteration;
        let mut m = scene_metric(ray.pos, objects);
        let k = m.inv * ray.p;
        let r = kerr_radius(ray.pos, vec3(0.0, 0.9375, 0.0));
        let dr = radius_rate(ray.pos, k.yzw(), r);
        if m.clearance <= 0.0001 {
            status = 1;
            break;
        }
        if r > 100.0 && dr > 0.0 {
            status = 2;
            break;
        }
        if affine > 21000.0 {
            break;
        }
        let mut h = next_h.min(
            (0.05 * r / k.yzw().length().max(1.0e-20))
                .min(0.25 * m.clearance / dr.abs().max(1.0e-20)),
        );
        if r < 101.0 {
            h = h.min(grid_step(ray.pos, k.yzw(), r, dr, header, settings.x));
        } else {
            h = h.min(0.5_f32.max((r - 100.0) / dr.abs().max(1.0e-8)));
        }
        last_h = h;
        let step = if dormand_prince != 0 {
            advance_ray_dp45::<false, GENERIC>(ray, h, &mut m, true, objects, &mut 0)
        } else {
            advance_ray_gauge(ray, h, &mut m, true, objects)
        };
        last_actual = step.h;
        last_error = step.error;
        if !step.accepted {
            status = 4;
            break;
        }
        let middle = Ray {
            pos: 0.5 * (ray.pos + step.ray.pos),
            p: 0.5 * (ray.p + step.ray.p),
            screen: 0.5 * (ray.screen + step.ray.screen),
        };
        let rm = kerr_radius(middle.pos, vec3(0.0, 0.9375, 0.0));
        let sm = sqrt(middle.pos.xz().dot(middle.pos.xz()) / (rm * rm + 0.9375 * 0.9375));
        if rm < 100.0 && sm > sin_00174 {
            let plasma = unsafe {
                sample_snapshot(middle.pos, header, primitives0, primitives1, physical_grid)
            };
            if !plasma.valid {
                status = 5;
                break;
            }
            if plasma.emitting && plasma.physical.x > 0.0 {
                let metric = scene_metric(middle.pos, objects);
                let normalization = seed.momentum.x / middle.p.x;
                let future = -(metric.inv * middle.p) * normalization;
                let energy = middle.p.dot(plasma.velocity) * normalization;
                let bcov = metric.g * plasma.magnetic;
                let bsq = plasma.magnetic.dot(bcov);
                let mu = clamp_f32(
                    future.dot(bcov) / (energy * sqrt(bsq.abs())).max(1.0e-20),
                    -1.0,
                    1.0,
                );
                let local = unsafe {
                    thermal_coefficients(plasma.physical.xyz(), 2.3e11 * energy, mu, thermal_bessel)
                };
                if !local.valid || !(energy > 0.0) {
                    status = 6;
                    break;
                }
                let mut c = local.coefficients;
                let frame = screen_frame(middle, metric);
                let e1 = vec4_f_v3(0.0, frame[0]);
                let e2 = vec4_f_v3(0.0, -frame[1]);
                let f1 = e1 + future * (e1.dot(metric.g * plasma.velocity) / energy);
                let f2 = e2 + future * (e2.dot(metric.g * plasma.velocity) / energy);
                let bproj = vec2(f1.dot(bcov), f2.dot(bcov));
                let b2 = bproj.dot(bproj);
                let mut rotation = vec2(1.0, 0.0);
                if b2 > 1.0e-20 {
                    rotation =
                        vec2(bproj.y * bproj.y - bproj.x * bproj.x, -2.0 * bproj.x * bproj.y) / b2;
                }
                c.emission = vec4_f_v2_f(c.emission.x, c.emission.y * rotation, c.emission.w);
                c.absorption =
                    vec4_f_v2_f(c.absorption.x, c.absorption.y * rotation, c.absorption.w);
                c.faraday = vec3_v2_f(c.faraday.x * rotation, c.faraday.z);
                let cell = transfer_cell(vec4_splat(0.0), c, energy * step.h / normalization);
                if !cell.valid {
                    next_h = 0.5 * step.h;
                    iteration += 1;
                    continue;
                }
                intensity += foreground * cell.stokes;
                foreground = foreground * cell.transmission;
            }
        }
        affine += step.h * ray.p.x / seed.momentum.x;
        ray = step.ray;
        ray.screen = vec4_f_v3(0.0, screen_frame(ray, m)[0]);
        let momentum_scale = ray
            .p
            .x
            .abs()
            .max(ray.p.y.abs())
            .max(ray.p.z.abs().max(ray.p.w.abs()));
        ray.p /= momentum_scale;
        max_null = max_null
            .max(ray.p.dot(m.inv * ray.p).abs() / ray.p.dot(ray.p).max(1.0e-10));
        next_h = momentum_scale
            * step.h
            * clamp_f32(0.9 * pow(5.0e-8 / step.error.max(1.0e-20), 0.2), 0.5, 2.0);
        iteration += 1;
    }
    let base = (4 * id) as usize;
    let final_metric = scene_metric(ray.pos, objects);
    unsafe {
        *pixels.add(base) = settings.w * camera_stokes(intensity, seed.jones);
        *pixels.add(base + 1) = vec4(steps as f32, status as f32, max_null, affine);
        *pixels.add(base + 2) = vec4_v3_f(ray.pos, final_metric.clearance);
        *pixels.add(base + 3) = vec4(last_h, last_actual, last_error, ray.p.x);
    }
}
