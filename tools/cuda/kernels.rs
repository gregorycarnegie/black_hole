// CUDA device kernels and physics helpers compiled to PTX by `cuda-oxide`.

use core::ops::{
    Add, AddAssign, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, Sub, SubAssign,
};

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
    pub _pad7: f32,
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

// -- Polarized transfer (polarized_transfer.wesl) ----------------------------

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

// -- Thermal coefficients (thermal.wesl) -------------------------------------

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

// -- Snapshot sampling (snapshot.wesl) ---------------------------------------

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

// -- Geodesic ray-tracer & Kerr-Schild metric (geodesic.wesl) ----------------

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

#[derive(Clone, Copy, Default)]
pub struct Metric {
    pub g: Mat4,
    pub inv: Mat4,
    pub dx: Mat4,
    pub dy: Mat4,
    pub dz: Mat4,
    pub clearance: f32,
    pub valid: bool,
}

#[inline(always)]
fn flat_metric() -> Metric {
    Metric {
        g: ETA,
        inv: ETA,
        dx: Mat4::default(),
        dy: Mat4::default(),
        dz: Mat4::default(),
        clearance: ESCAPE_R,
        valid: true,
    }
}

#[cuda_device::device]
fn add_kerr(base: Metric, x: Vec3, mass: f32, spin: Vec3) -> Metric {
    let mut m = base;
    if mass <= 0.0 {
        return m;
    }
    let inv_spin_scale = 1.0 / (spin.length() / 0.999).max(1.0);
    let a = mass * spin * inv_spin_scale;
    let a2 = a.dot(a);
    let ax = a.dot(x);
    let raw_r = kerr_radius(x, a);
    let horizon = mass + sqrt((mass * mass - a2).max(0.0));
    m.clearance = m.clearance.min(raw_r - horizon);
    let r = raw_r.max(0.8 * horizon);
    let r2 = r * r;
    let den = r2 * r2 + ax * ax;
    let inv_r = 1.0 / r;
    let inv_r2 = 1.0 / r2;
    let inv_den = 1.0 / den;
    let inv_r2_a2 = 1.0 / (r2 + a2);
    let h = mass * r * r2 * inv_den;
    let numerator = r * x - a.cross(x) + (ax * inv_r) * a;
    let ell = vec4_f_v3(1.0, numerator * inv_r2_a2);
    let ll = outer(ell, ell);
    let inv_dr = 1.0 / (2.0 * r2 - x.dot(x) + a2).max(1.0e-12);
    let dr = (r * x + (ax * inv_r) * a) * inv_dr;
    // Constant axes keep the derivative matrices in registers instead of local memory.
    let derivative = |ej: Vec3, dr_j: f32, a_j: f32| {
        let dh = h * (3.0 * dr_j * inv_r - (4.0 * r * r2 * dr_j + 2.0 * ax * a_j) * inv_den);
        let dn = dr_j * x + r * ej - a.cross(ej) + (a_j * inv_r - ax * dr_j * inv_r2) * a;
        let dl = vec4_f_v3(0.0, (dn - ell.yzw() * 2.0 * r * dr_j) * inv_r2_a2);
        2.0 * dh * ll + 2.0 * h * (outer(dl, ell) + outer(ell, dl))
    };
    m.g += 2.0 * h * ll;
    m.dx += derivative(vec3(1.0, 0.0, 0.0), dr.x, a.x);
    m.dy += derivative(vec3(0.0, 1.0, 0.0), dr.y, a.y);
    m.dz += derivative(vec3(0.0, 0.0, 1.0), dr.z, a.z);
    let raised = m.inv * ell;
    let divisor = 1.0 + 2.0 * h * ell.dot(raised);
    if divisor <= 1.0e-6 {
        m.valid = false;
        return m;
    }
    m.inv -= (2.0 * h / divisor) * outer(raised, raised);
    m.valid = m.valid && m.inv[0][0] < -1.0e-6;
    m
}

#[cuda_device::device]
fn scene_metric(pos: Vec3, objects: &Objects) -> Metric {
    let mut m = flat_metric();
    let mut i = 0i32;
    while i < objects.num_objects {
        let idx = i as usize;
        m = add_kerr(
            m,
            pos - objects.pos_radius[idx].xyz(),
            objects.mass[idx].x.max(0.0),
            objects.spin[idx].xyz(),
        );
        i += 1;
    }
    m
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

#[cuda_device::device]
fn geodesic_rhs(ray: Ray, m: Metric) -> Derivs {
    let k = m.inv * ray.p;
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
            * (m.inv
                * ((k.y * dx_f + k.z * dy_f + k.w * dz_f)
                    + (ray.screen.y * dx_k + ray.screen.z * dy_k + ray.screen.w * dz_k)
                    - contracted)),
    }
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

#[inline(always)]
fn ray_rhs(ray: Ray, m: Metric, gauged: bool) -> Derivs {
    let mut result = geodesic_rhs(ray, m);
    if gauged {
        let k = m.inv * ray.p;
        if k.x.abs() > 1.0e-20 {
            result.screen -= k * (result.screen.x / k.x);
            result.screen.x = 0.0;
        }
    }
    result
}

#[cuda_device::device]
fn step_ray_gauge(ray: Ray, h: f32, m: Metric, gauged: bool, objects: &Objects) -> RayStep {
    if !ray_valid(ray, m) {
        return RayStep { ray, valid: false };
    }
    let k1 = ray_rhs(ray, m, gauged);
    let r2 = rk_state(ray, k1, 0.5 * h);
    let m2 = scene_metric(r2.pos, objects);
    if !ray_valid(r2, m2) {
        return RayStep { ray, valid: false };
    }
    let k2 = ray_rhs(r2, m2, gauged);
    let r3 = rk_state(ray, k2, 0.5 * h);
    let m3 = scene_metric(r3.pos, objects);
    if !ray_valid(r3, m3) {
        return RayStep { ray, valid: false };
    }
    let k3 = ray_rhs(r3, m3, gauged);
    let r4 = rk_state(ray, k3, h);
    let m4 = scene_metric(r4.pos, objects);
    if !ray_valid(r4, m4) {
        return RayStep { ray, valid: false };
    }
    let k4 = ray_rhs(r4, m4, gauged);
    let next = rk_state(
        ray,
        Derivs {
            pos: k1.pos + 2.0 * k2.pos + 2.0 * k3.pos + k4.pos,
            p: k1.p + 2.0 * k2.p + 2.0 * k3.p + k4.p,
            screen: k1.screen + 2.0 * k2.screen + 2.0 * k3.screen + k4.screen,
        },
        h / 6.0,
    );
    RayStep {
        ray: next,
        valid: ray_valid(next, scene_metric(next.pos, objects)),
    }
}

#[inline(always)]
fn step_ray(ray: Ray, h: f32, m: Metric, objects: &Objects) -> RayStep {
    step_ray_gauge(ray, h, m, false, objects)
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
}

#[cuda_device::device]
fn advance_ray_gauge(
    ray: Ray,
    requested_h: f32,
    m: Metric,
    gauged: bool,
    objects: &Objects,
) -> AdaptiveStep {
    if !(requested_h > 0.0 && requested_h < 1.0e8) {
        return AdaptiveStep {
            ray,
            h: 0.0,
            error: 1.0e30,
            accepted: false,
        };
    }
    let mut h = requested_h;
    let mut retry = 0u32;
    while retry < 12 {
        let coarse = step_ray_gauge(ray, h, m, gauged, objects);
        if coarse.valid {
            let half = step_ray_gauge(ray, 0.5 * h, m, gauged, objects);
            if half.valid {
                let fine = step_ray_gauge(
                    half.ray,
                    0.5 * h,
                    scene_metric(half.ray.pos, objects),
                    gauged,
                    objects,
                );
                if fine.valid {
                    let error = relative_difference(
                        vec4_v3_f(coarse.ray.pos, 0.0),
                        vec4_v3_f(fine.ray.pos, 0.0),
                    )
                    .max(
                        relative_difference(coarse.ray.p, fine.ray.p)
                            .max(relative_difference(coarse.ray.screen, fine.ray.screen)),
                    ) / 15.0;
                    let metric = scene_metric(fine.ray.pos, objects);
                    let null_error = fine.ray.p.dot(metric.inv * fine.ray.p).abs()
                        / fine.ray.p.dot(fine.ray.p).max(1.0e-10);
                    if error <= STEP_TOLERANCE
                        && null_error < 2.0e-4
                        && (fine.ray.pos.x != ray.pos.x
                            || fine.ray.pos.y != ray.pos.y
                            || fine.ray.pos.z != ray.pos.z)
                    {
                        return AdaptiveStep {
                            ray: fine.ray,
                            h,
                            error,
                            accepted: true,
                        };
                    }
                }
            }
        }
        h *= 0.5;
        retry += 1;
    }
    AdaptiveStep {
        ray,
        h: 0.0,
        error: 1.0e30,
        accepted: false,
    }
}

#[inline(always)]
fn advance_ray(ray: Ray, requested_h: f32, m: Metric, objects: &Objects) -> AdaptiveStep {
    advance_ray_gauge(ray, requested_h, m, false, objects)
}

#[cuda_device::device]
fn screen_frame(ray: Ray, m: Metric) -> Mat3 {
    let k = m.inv * ray.p;
    let shift = -m.inv[0].yzw() * (1.0 / m.inv[0][0]);
    let gamma = spatial_metric(m);
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
    if w * ds < 1.0e-5 {
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
    let m = scene_metric(ray.pos, objects);
    let density = 0.4 * exp(-0.5 * z * z) * disk_edge_fade(r, disk) / height;
    let k = m.inv * ray.p;
    let omega = sub_keplerian_factor(h_r) / (r * sqrt(r) + disk.spin).max(1.0e-3);
    let tangent = vec3(ray.pos.z, 0.0, -ray.pos.x);
    let mut fluid = vec4_f_v3(1.0, omega * tangent);
    let norm = fluid.dot(m.g * fluid);
    if norm < -1.0e-4 {
        fluid *= inverse_sqrt(-norm);
    } else {
        let lapse = inverse_sqrt(-m.inv[0][0]);
        fluid = -lapse * m.inv[0];
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
    let frame = screen_frame(ray, m);
    let mut e1 = vec4_f_v3(0.0, frame[0]);
    let mut e2 = vec4_f_v3(0.0, frame[1]);
    e1 -= k * (e1.dot(m.g * fluid) / plasma.energy);
    e2 -= k * (e2.dot(m.g * fluid) / plasma.energy);
    let mut b = vec4_f_v3(0.0, tangent.normalize());
    b += fluid * b.dot(m.g * fluid);
    b *= inverse_sqrt(b.dot(m.g * b).max(1.0e-12));
    let bx = b.dot(m.g * e1);
    let by = b.dot(m.g * e2);
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
    let bparallel = -b.dot(m.g * k) / plasma.energy;
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
    let pix_x = gid_x();
    let pix_y = gid_y();
    if pix_x >= width || pix_y >= height {
        return;
    }
    let cam = unsafe { &*cam };
    let disk = unsafe { &*disk };
    let objects = unsafe { &*objects };
    let idx = (pix_y * width + pix_x) as usize;

    let u = (2.0 * (pix_x as f32 + 0.5 + cam.jitter_x) / width as f32 - 1.0)
        * cam.aspect
        * cam.tan_half_fov;
    let v = (1.0 - 2.0 * (pix_y as f32 + 0.5 + cam.jitter_y) / height as f32) * cam.tan_half_fov;
    let dir = (u * cam.right - v * cam.up + cam.forward).normalize();
    let mut metric = scene_metric(cam.pos, objects);
    if !metric.valid || metric.clearance <= 0.0 {
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
    let mut i = 0u32;
    while i < cam.max_iter {
        iterations = i + 1;
        if metric.clearance < 0.002 || !metric.valid {
            break;
        }
        let velocity = (metric.inv * ray.p).yzw();
        let mut distance = clamp_f32(0.12 * metric.clearance, 0.0002, 32.0);
        let radius = disk_radius(ray.pos, disk.spin, disk.binary_enabled != 0);
        if radius > disk.r1 - distance && radius < disk.r2 + distance {
            let r_clamped = radius.max(disk.r1);
            let height_d = (get_h_over_r(r_clamped, disk) * r_clamped).max(0.001);
            let mid = disk_midplane_y(radius.max(0.001), ray.pos.xz(), disk);
            let to_disk = ((ray.pos.y - mid).abs() - 4.0 * height_d).max(0.0);
            distance = distance.min((0.25 * height_d).max(0.5 * to_disk));
        }
        let step = advance_ray(
            ray,
            (distance / velocity.length().max(1.0e-6)).min(next_h),
            metric,
            objects,
        );
        // Stop when the affine parameter can no longer advance in binary32.
        if !step.accepted || affine + step.h == affine {
            break;
        }
        affine += step.h;
        let h = step.h;
        let next = step.ray;
        let next_metric = scene_metric(next.pos, objects);
        next_h = h * clamp_f32(0.9 * pow(STEP_TOLERANCE / step.error.max(1.0e-20), 0.2), 0.5, 2.0);
        let hit = intersect_objects_segment(ray.pos, next.pos, objects);
        if hit.hit {
            let intensity = hit.color.xyz().dot(vec3(0.2126, 0.7152, 0.0722));
            rgb += transmission * hit.color.xyz();
            stokes.x += transmission * intensity;
            break;
        }
        let middle = Ray {
            pos: 0.5 * (ray.pos + next.pos),
            p: 0.5 * (ray.p + next.p),
            screen: 0.5 * (ray.screen + next.screen),
        };
        let plasma = sample_plasma(middle, objects, cam, disk);
        let ds = h * plasma.energy;
        if ds > 0.0 {
            if cam.polarization_view != 0 {
                let cell = polarized_cell(plasma.j, plasma.alpha, plasma.rho, ds);
                stokes += transmission * vec4_f_v3(cell.x, foreground * cell.yzw());
                foreground = foreground * faraday_rotation(plasma.rho, ds);
            }
            rgb += transmission * plasma.rgb * absorption_integral(plasma.alpha, ds);
            transmission *= exp(-plasma.alpha * ds);
        }
        ray = next;
        metric = next_metric;
        let frame = screen_frame(ray, metric);
        ray.screen = vec4_f_v3(0.0, frame[0]);
        if ray.pos.length() > ESCAPE_R {
            let sky = unsafe {
                sample_skybox(
                    (metric.inv * ray.p).yzw().normalize(),
                    skybox,
                    sky_w as i32,
                    sky_h as i32,
                )
            };
            rgb += transmission * sky;
            stokes.x += transmission * sky.dot(vec3(0.2126, 0.7152, 0.0722));
            break;
        }
        if transmission < 0.001 {
            break;
        }
        i += 1;
    }
    let mut output = tonemap(rgb);
    if cam.polarization_view != 0 {
        output = polarization_color(stokes, cam);
    }
    if cam.debug_heatmap != 0 {
        output = heatmap_color(iterations as f32 / cam.max_iter.max(1) as f32);
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
fn verification_metric(pos: Vec3, binary: bool) -> Metric {
    if binary {
        return add_kerr(
            add_kerr(
                flat_metric(),
                pos + vec3(7.0, 0.0, 0.0),
                0.5,
                vec3_splat(0.0),
            ),
            pos - vec3(7.0, 0.0, 0.0),
            0.5,
            vec3_splat(0.0),
        );
    }
    add_kerr(
        flat_metric(),
        pos + vec3(7.0, 0.0, 0.0),
        1.0,
        vec3_splat(0.0),
    )
}

#[inline(always)]
fn metric_derivative(m: Metric, i: u32) -> Mat4 {
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
fn connection(m: Metric, a: u32, b: u32, c: u32) -> f32 {
    let db = metric_derivative(m, b);
    let dc = metric_derivative(m, c);
    let mut value = 0.0_f32;
    let mut d = 0u32;
    while d < 4 {
        let dd = metric_derivative(m, d);
        value += 0.5 * m.inv[d][a] * (db[c][d] + dc[b][d] - dd[c][b]);
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
    let m = add_kerr(flat_metric(), x, 0.7, spin);
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
        let mut analytic = m.dx;
        if i == 5 {
            analytic = m.dy;
        }
        if i == 6 {
            analytic = m.dz;
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
    let mut m = Metric::default();
    unsafe {
        m.inv = read_matrix(inputs, b);
        m.dx = read_matrix(inputs, b + 16);
        m.dy = read_matrix(inputs, b + 32);
        m.dz = read_matrix(inputs, b + 48);
        let d = geodesic_rhs(
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
    let mut next_h = 1.0e8_f32;
    let mut status = 0.0_f32;
    let mut steps = 0u32;
    let mut i = 0u32;
    while i < 10000 {
        if metric.clearance < 0.002 || !metric.valid {
            status = 1.0;
            break;
        }
        let velocity = (metric.inv * ray.p).yzw();
        let distance = clamp_f32(0.12 * metric.clearance, 0.0002, 32.0);
        let step = advance_ray(
            ray,
            (distance / velocity.length().max(1.0e-6)).min(next_h),
            metric,
            objects,
        );
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
    let base = (4 * id) as usize;
    unsafe {
        *results.add(base) = vec4_v3_f(start.pos, status);
        *results.add(base + 1) = start.p;
        *results.add(base + 2) = vec4_v3_f(ray.pos, steps as f32);
        *results.add(base + 3) = vec4_v3_f(ray.p.yzw(), 0.0);
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
        let step = advance_ray(ray, wanted, metric, objects);
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
    let base = (4 * id) as usize;
    unsafe {
        *results.add(base) = vec4_v3_f(start.pos, status);
        *results.add(base + 1) = start.p;
        *results.add(base + 2) = vec4_v3_f(ray.pos, affine);
        *results.add(base + 3) = vec4_v3_f(ray.p.yzw(), steps as f32);
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
        let m = scene_metric(ray.pos, objects);
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
        let step = advance_ray_gauge(ray, h, m, true, objects);
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
        let endpoint_metric = scene_metric(ray.pos, objects);
        ray.screen = vec4_f_v3(0.0, screen_frame(ray, endpoint_metric)[0]);
        let momentum_scale = ray
            .p
            .x
            .abs()
            .max(ray.p.y.abs())
            .max(ray.p.z.abs().max(ray.p.w.abs()));
        ray.p /= momentum_scale;
        let metric = scene_metric(ray.pos, objects);
        max_null = max_null
            .max(ray.p.dot(metric.inv * ray.p).abs() / ray.p.dot(ray.p).max(1.0e-10));
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
