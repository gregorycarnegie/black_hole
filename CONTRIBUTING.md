# Contributing

Thanks for helping. This guide covers setting up, checking a change and opening a pull request. The [README](README.md#running) explains how to run the simulation.

## Before you start

- For a large change, open an issue first so the approach can be agreed before you write it.
- Pull requests go to `main`. Keep each one to a single change, and explain what it changes and how you checked it.
- Add a line under `## Unreleased` in [CHANGELOG.md](CHANGELOG.md) for anything a user or contributor would notice.

## Checks every pull request must pass

CI runs these without a GPU: the Rust checks on Linux and Windows, the Python checks on Linux. Run them locally first:

```bash
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --all-targets
python -m pip install -r verification/requirements-data.txt
python -m unittest discover -s verification -v
```

`cargo test` runs the unit, `rstest` and `proptest` tests, which need no GPU. For new tests, prefer `rstest` case tables and `proptest` invariants where they fit.

Rustfmt is not enforced. Format only the code you change, so that the diff stays reviewable.

## GPU tests

Tests that need an NVIDIA GPU are marked `#[ignore = "requires a CUDA GPU"]`, and CI skips them. If you change the renderer, the CUDA kernels or the swarm, run them on a machine that meets the [requirements](README.md#requirements):

```bash
cargo test --release -- --ignored
```

Benchmark tests print their timings with `--nocapture`, for example `cargo test --release --bin black_hole -- --ignored swarm_bvh_against_brute_force --nocapture`. Record measured speed changes in [RENDERING_PERFORMANCE.md](RENDERING_PERFORMANCE.md).

## Changing the CUDA kernels

The kernels are written in Rust in [`tools/cuda/kernels.rs`](tools/cuda/kernels.rs) and compiled to PTX by [cuda-oxide](https://github.com/NVIDIA/cuda-rust). The generated [`src/compute/kernels.ptx`](src/compute/kernels.ptx) is committed, so that the simulation builds without cuda-oxide. After editing the kernels, regenerate it and commit it with your change:

```bash
python tools/cuda/build.py
```

The first line of the PTX records a hash of its sources. The `ptx_matches_cuda_oxide_kernel_sources` test fails if the kernels changed and the PTX was not regenerated.

cuda-oxide runs on Linux, and on Windows `build.py` runs it in WSL. Install it in that environment, pinned to the revision this project uses:

```bash
cargo install --git https://github.com/NVIDIA/cuda-rust.git \
  --rev e027ac324f663e8408c13c116d7dddd58d5e8daf cargo-oxide
```

[`tools/cuda/oxide/rust-toolchain.toml`](tools/cuda/oxide/rust-toolchain.toml) pins the nightly toolchain that it needs.

## Changing the OptiX programs

The OptiX programs in [`tools/optix/programs.rs`](tools/optix/programs.rs) are also built with cuda-oxide. Build them from `tools/optix` (on Windows, inside WSL) and commit the regenerated `black_hole_optix_programs.ptx`:

```bash
cargo oxide build --arch sm_80
```

To check the result, build with `--features optix` (see the [README](README.md#optional-rtx-optix-build)) and run `optix_renders_the_brute_force_image` with `--ignored`. It compares the OptiX image with brute force bit for bit.

**Never commit the OptiX SDK headers, or files generated from them.** The OptiX licence allows building against the headers, but not redistributing them. `build.rs` writes the generated bindings to Cargo's `OUT_DIR`, outside the repository.

## Proofs and verification

The Lean 4 proofs and their numerical checks are in [`verification/`](verification/README.md). If you change a modelled kernel, a fixture or a proof, follow that README, which mainly means running `python check.py` there. A separate workflow rebuilds the proofs when `.lean` files or the Lean toolchain change. Some kernels have proofs about them, and changing their arithmetic can make the proofs or the fixture hashes out of date. [`verification/OBLIGATIONS.md`](verification/OBLIGATIONS.md) lists what is proved and what is still assumed.

## Mutation testing (optional)

`cargo mutants -j6` checks whether the tests catch deliberate changes to the code. Exclusions and their reasons are in `.cargo/mutants.toml`.
