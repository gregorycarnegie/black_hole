use black_hole::cuda::shared_cuda;
use cudarc::driver::{LaunchConfig, PushKernelArg};

pub fn atan2(points: &[[f32; 2]]) -> Vec<f32> {
    let cuda = shared_cuda();
    cuda.run_1d(&cuda.test_atan2, points, 64)
}

pub fn sincos(angles: &[f32]) -> Vec<[f32; 2]> {
    let cuda = shared_cuda();
    cuda.run_1d(&cuda.test_sincos, angles, 64)
}

pub fn geodesic_rhs(inputs: &[f32], cases: usize) -> Vec<f32> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let count = u32::try_from(cases).unwrap();
    let d_in = cuda.clone_htod(inputs);
    let mut d_out = cuda.alloc_zeros::<f32>(cases * 11);

    let cfg = LaunchConfig {
        grid_dim: (count.div_ceil(64), 1, 1),
        block_dim: (64, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_geodesic_rhs);
    builder.arg(&d_in);
    builder.arg(&mut d_out);
    builder.arg(&count);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_geodesic_rhs launch failed");
    }
    cuda.clone_dtoh(&d_out)
}

pub fn energies(cam: &[u8], dsk: &[u8], objects: &[u8]) -> Vec<f32> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let d_cam = cuda.clone_htod(cam);
    let d_dsk = cuda.clone_htod(dsk);
    let d_obj = cuda.clone_htod(objects);
    let mut d_out = cuda.alloc_zeros::<f32>(32 * 32 * 4);

    let cfg = LaunchConfig {
        grid_dim: (4, 1, 1),
        block_dim: (8, 8, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_energy);
    builder.arg(&d_cam);
    builder.arg(&d_dsk);
    builder.arg(&d_obj);
    builder.arg(&mut d_out);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_energy launch failed");
    }
    cuda.clone_dtoh(&d_out)
}

pub fn controller_trace(objects: &[u8], input: &[u8], count: u32) -> Vec<f32> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let d_obj = cuda.clone_htod(objects);
    let d_in = cuda.clone_htod(input);
    let mut d_out = cuda.alloc_zeros::<f32>((count as usize) * 16);

    let cfg = LaunchConfig {
        grid_dim: (count, 1, 1),
        block_dim: (1, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_controller_trace);
    builder.arg(&d_obj);
    builder.arg(&d_in);
    builder.arg(&mut d_out);
    builder.arg(&count);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_controller_trace launch failed");
    }
    cuda.clone_dtoh(&d_out)
}

pub fn controller_classify(objects: &[u8], input: &[u8], count: u32) -> Vec<f32> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let d_obj = cuda.clone_htod(objects);
    let d_in = cuda.clone_htod(input);
    let mut d_out = cuda.alloc_zeros::<f32>((count as usize) * 16);

    let cfg = LaunchConfig {
        grid_dim: (count, 1, 1),
        block_dim: (1, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_controller_classify);
    builder.arg(&d_obj);
    builder.arg(&d_in);
    builder.arg(&mut d_out);
    builder.arg(&count);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_controller_classify launch failed");
    }
    cuda.clone_dtoh(&d_out)
}

pub fn snapshot(
    header: &[u8],
    p0: &[u8],
    p1: &[u8],
    phys: &[u8],
    positions: &[u8],
    count: u32,
) -> Vec<u8> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let d_header = cuda.clone_htod(header);
    let d_p0 = cuda.clone_htod(p0);
    let d_p1 = cuda.clone_htod(p1);
    let d_phys = cuda.clone_htod(phys);
    let d_pos = cuda.clone_htod(positions);
    let mut d_out = cuda.alloc_zeros::<u8>((count as usize) * 64);

    let cfg = LaunchConfig {
        grid_dim: (count.div_ceil(64), 1, 1),
        block_dim: (64, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_snapshot);
    builder.arg(&d_header);
    builder.arg(&d_p0);
    builder.arg(&d_p1);
    builder.arg(&d_phys);
    builder.arg(&d_pos);
    builder.arg(&mut d_out);
    builder.arg(&count);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_snapshot launch failed");
    }
    cuda.clone_dtoh(&d_out)
}

pub fn thermal(table: &[u8], cases: &[u8], count: u32) -> Vec<u8> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let d_table = cuda.clone_htod(table);
    let d_cases = cuda.clone_htod(cases);
    let mut d_out = cuda.alloc_zeros::<u8>((count as usize) * 48);

    let cfg = LaunchConfig {
        grid_dim: (count.div_ceil(64), 1, 1),
        block_dim: (64, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_thermal);
    builder.arg(&d_table);
    builder.arg(&d_cases);
    builder.arg(&mut d_out);
    builder.arg(&count);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_thermal launch failed");
    }
    cuda.clone_dtoh(&d_out)
}

pub fn transfer(cases: &[u8], count: u32) -> Vec<u8> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let d_cases = cuda.clone_htod(cases);
    let mut d_out = cuda.alloc_zeros::<u8>((count as usize) * 32);

    let cfg = LaunchConfig {
        grid_dim: (count.div_ceil(64), 1, 1),
        block_dim: (64, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_transfer);
    builder.arg(&d_cases);
    builder.arg(&mut d_out);
    builder.arg(&count);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_transfer launch failed");
    }
    cuda.clone_dtoh(&d_out)
}

#[allow(clippy::too_many_arguments)]
pub fn image(
    objects: &[u8],
    header: &[u8],
    p0: &[u8],
    p1: &[u8],
    phys: &[u8],
    table: &[u8],
    seeds: &[u8],
    settings: &[u8],
    count: u32,
) -> Vec<u8> {
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let d_obj = cuda.clone_htod(objects);
    let d_header = cuda.clone_htod(header);
    let d_p0 = cuda.clone_htod(p0);
    let d_p1 = cuda.clone_htod(p1);
    let d_phys = cuda.clone_htod(phys);
    let d_table = cuda.clone_htod(table);
    let d_seeds = cuda.clone_htod(seeds);
    let d_settings = cuda.clone_htod(settings);
    let mut d_out = cuda.alloc_zeros::<u8>((count as usize) * 64);

    let cfg = LaunchConfig {
        grid_dim: (count.div_ceil(32), 1, 1),
        block_dim: (32, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.test_image);
    builder.arg(&d_obj);
    builder.arg(&d_header);
    builder.arg(&d_p0);
    builder.arg(&d_p1);
    builder.arg(&d_phys);
    builder.arg(&d_table);
    builder.arg(&d_seeds);
    builder.arg(&d_settings);
    builder.arg(&mut d_out);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_test_image launch failed");
    }
    cuda.clone_dtoh(&d_out)
}
