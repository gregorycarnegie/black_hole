use std::sync::{Arc, OnceLock};

use cudarc::{
    driver::{
        CudaContext, CudaFunction, CudaModule, CudaSlice, CudaStream, DeviceRepr, LaunchConfig,
        PushKernelArg, ValidAsZeroBits, result, sys,
    },
    nvrtc::Ptx,
};

pub const PTX: &str = include_str!("kernels.ptx");

pub const KERNEL_NAMES: [&str; 13] = [
    "bh_geodesic",
    "bh_accumulate",
    "bh_check_relativity",
    "bh_test_atan2",
    "bh_test_sincos",
    "bh_test_geodesic_rhs",
    "bh_test_energy",
    "bh_test_controller_classify",
    "bh_test_controller_trace",
    "bh_test_snapshot",
    "bh_test_thermal",
    "bh_test_transfer",
    "bh_test_image",
];

const MEMPOOL_RELEASE_THRESHOLD_BYTES: u64 = 512 << 20;

pub struct CudaKernels {
    pub context: Arc<CudaContext>,
    pub stream: Arc<CudaStream>,
    pub module: Arc<CudaModule>,
    pub geodesic: CudaFunction,
    pub accumulate: CudaFunction,
    pub check_relativity: CudaFunction,
    pub test_atan2: CudaFunction,
    pub test_sincos: CudaFunction,
    pub test_geodesic_rhs: CudaFunction,
    pub test_energy: CudaFunction,
    pub test_controller_classify: CudaFunction,
    pub test_controller_trace: CudaFunction,
    pub test_snapshot: CudaFunction,
    pub test_thermal: CudaFunction,
    pub test_transfer: CudaFunction,
    pub test_image: CudaFunction,
}

pub fn shared_cuda() -> &'static CudaKernels {
    static INSTANCE: OnceLock<CudaKernels> = OnceLock::new();
    INSTANCE.get_or_init(|| CudaKernels::new(0).expect("failed to initialize CUDA runtime"))
}

impl CudaKernels {
    pub fn new(ordinal: usize) -> Result<Self, String> {
        let context = CudaContext::new(ordinal).map_err(|err| format!("CUDA init: {err}"))?;
        let cu_device = context.cu_device();
        unsafe {
            if let Ok(mempool) = result::device::get_mem_pool(cu_device) {
                let mut threshold = MEMPOOL_RELEASE_THRESHOLD_BYTES;
                let _ = sys::cuMemPoolSetAttribute(
                    mempool,
                    sys::CUmemPool_attribute::CU_MEMPOOL_ATTR_RELEASE_THRESHOLD,
                    (&mut threshold as *mut u64).cast(),
                );
            }
            context.disable_event_tracking();
        }

        let stream = context.default_stream();
        let module = context
            .load_module(Ptx::from_src(PTX))
            .map_err(|err| format!("CUDA PTX load: {err}"))?;

        let load = |name: &str| {
            module
                .load_function(name)
                .map_err(|err| format!("CUDA load function `{name}`: {err}"))
        };

        Ok(Self {
            geodesic: load("bh_geodesic")?,
            accumulate: load("bh_accumulate")?,
            check_relativity: load("bh_check_relativity")?,
            test_atan2: load("bh_test_atan2")?,
            test_sincos: load("bh_test_sincos")?,
            test_geodesic_rhs: load("bh_test_geodesic_rhs")?,
            test_energy: load("bh_test_energy")?,
            test_controller_classify: load("bh_test_controller_classify")?,
            test_controller_trace: load("bh_test_controller_trace")?,
            test_snapshot: load("bh_test_snapshot")?,
            test_thermal: load("bh_test_thermal")?,
            test_transfer: load("bh_test_transfer")?,
            test_image: load("bh_test_image")?,
            context,
            stream,
            module,
        })
    }

    pub fn bind_to_thread(&self) {
        self.context
            .bind_to_thread()
            .expect("failed to bind CUDA context to current thread");
    }

    pub fn alloc_zeros<T: DeviceRepr + ValidAsZeroBits>(&self, len: usize) -> CudaSlice<T> {
        self.bind_to_thread();
        self.stream
            .alloc_zeros::<T>(len)
            .expect("CUDA alloc_zeros failed")
    }

    pub fn clone_htod<T: DeviceRepr + Copy>(&self, data: &[T]) -> CudaSlice<T> {
        self.bind_to_thread();
        self.stream
            .clone_htod(data)
            .expect("CUDA clone_htod failed")
    }

    pub fn memcpy_htod<T: DeviceRepr + Copy>(&self, src: &[T], dst: &mut CudaSlice<T>) {
        self.bind_to_thread();
        self.stream
            .memcpy_htod(src, dst)
            .expect("CUDA memcpy_htod failed");
    }

    pub fn clone_dtoh<T: DeviceRepr + Copy>(&self, src: &CudaSlice<T>) -> Vec<T> {
        self.bind_to_thread();
        self.stream.clone_dtoh(src).expect("CUDA clone_dtoh failed")
    }

    pub fn memcpy_dtoh<T: DeviceRepr + Copy>(&self, src: &CudaSlice<T>, dst: &mut [T]) {
        self.bind_to_thread();
        self.stream
            .memcpy_dtoh(src, dst)
            .expect("CUDA memcpy_dtoh failed");
    }

    /// Run a 1D kernel `func(inputs, count, outputs)` and return the output vector.
    pub fn run_1d<I, O>(&self, func: &CudaFunction, inputs: &[I], block_size: u32) -> Vec<O>
    where
        I: bytemuck::Pod,
        O: bytemuck::Pod,
    {
        assert!(!inputs.is_empty(), "GPU input batch must not be empty");
        self.bind_to_thread();
        let count = u32::try_from(inputs.len()).expect("input batch count fits in u32");
        let in_bytes: &[u8] = bytemuck::cast_slice(inputs);
        let out_byte_len = inputs
            .len()
            .checked_mul(std::mem::size_of::<O>())
            .expect("output byte size overflow");

        let d_in = self.clone_htod(in_bytes);
        let mut d_out = self.alloc_zeros::<u8>(out_byte_len);

        let cfg = LaunchConfig {
            grid_dim: (count.div_ceil(block_size), 1, 1),
            block_dim: (block_size, 1, 1),
            shared_mem_bytes: 0,
        };
        let mut builder = self.stream.launch_builder(func);
        builder.arg(&d_in);
        builder.arg(&mut d_out);
        builder.arg(&count);
        unsafe {
            builder.launch(cfg).expect("CUDA 1D kernel launch failed");
        }
        let out_bytes = self.clone_dtoh(&d_out);
        bytemuck::cast_slice::<u8, O>(&out_bytes).to_vec()
    }
}

pub fn ptx_recorded_sha256() -> Option<&'static str> {
    PTX.lines()
        .next()
        .and_then(|line| line.strip_prefix("// Source SHA256: "))
        .map(str::trim)
}

pub fn kernels_source_sha256() -> String {
    const SOURCES: [(&str, &[u8]); 5] = [
        (
            "tools/cuda/kernels.rs",
            include_bytes!("../../tools/cuda/kernels.rs"),
        ),
        (
            "tools/cuda/oxide/Cargo.toml",
            include_bytes!("../../tools/cuda/oxide/Cargo.toml"),
        ),
        (
            "tools/cuda/oxide/Cargo.lock",
            include_bytes!("../../tools/cuda/oxide/Cargo.lock"),
        ),
        (
            "tools/cuda/oxide/rust-toolchain.toml",
            include_bytes!("../../tools/cuda/oxide/rust-toolchain.toml"),
        ),
        (
            "tools/cuda/oxide/src/main.rs",
            include_bytes!("../../tools/cuda/oxide/src/main.rs"),
        ),
    ];

    let mut msg = Vec::new();
    for (rel, bytes) in SOURCES {
        msg.extend_from_slice(rel.as_bytes());
        msg.push(0);
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'\r' && i + 1 < bytes.len() && bytes[i + 1] == b'\n' {
                msg.push(b'\n');
                i += 2;
            } else {
                msg.push(bytes[i]);
                i += 1;
            }
        }
        msg.push(0);
    }
    sha256_hex(&msg)
}

fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    let bit_len = (data.len() as u64) * 8;
    let mut padded = data.to_vec();
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = String::with_capacity(64);
    for word in h {
        use std::fmt::Write as _;
        let _ = write!(&mut out, "{word:08x}");
    }
    out
}
