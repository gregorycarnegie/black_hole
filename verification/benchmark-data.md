# EHT comparison input and reference solver

The required snapshot was found publicly and downloaded on 2026-11-03.
Cora Prather's [Harvard Dataverse archive](https://doi.org/10.7910/DVN/XZECPF),
version 1.2, identifies it as the input used in the EHT polarized-code
comparison. It has a CC0-1.0 license. The public download was discovered in the
[GPUmonty authors' instructions](https://github.com/black-hole-group/gpumonty/blob/21a00ce7e415241e9b6e498f44a7a0173be1c832/README.md).
The older paper's request-only availability statement is superseded by this
archive; its imaging parameters remain the reference.

## Verified input

[fixtures/eht-snapshot.json](fixtures/eht-snapshot.json) pins the metadata.

| Item | Value |
| --- | --- |
| Archive file ID | 12137142 |
| Filename | `sample_dump_SANE_a+0.94_MKS_0900.h5` |
| Size | 302010648 bytes |
| Published MD5 | `dc8cf9b45136cd9b28bdb8ed197cfd69` |
| Verified SHA-256 | `c2d1dfdc8c92320ec77d22953f55c2b5d71b685496f5199c73a1280f20a0d537` |
| Spin | 0.9375 |
| Grid | 288 × 128 × 128 |
| Coordinates | MKS |
| Primitive order | RHO, UU, U1, U2, U3, B1, B2, B3 |
| Primitive shape / type | (288, 128, 128, 8), binary32 |
| Nominal time in paper | 4500 GM/c³ |
| Actual file-header time | 4501.677840911209 GM/c³ |
| Adiabatic index in file | 1.444444 |

All primitive values are finite; density and internal energy are positive.
The file also records 1902 nonzero `extras/fail` cells, 360738 nonzero
`extras/fixup` cells, and maximum absolute `extras/divB` of about 3.655×10⁻⁷.
These are diagnostics from the archived simulation, not proof that it is
error-free. Their semantics, numerical floors and reference treatment must
be accounted for during calibration. The time must not be silently rounded
to the paper's nominal value. The archive checksum identifies the exact file.

## Acquire and inspect

Run these PowerShell commands from the repository root. All downloaded data
and Python packages stay under the ignored `target/` directory.

```powershell
python -m venv target/verification-python
target/verification-python/Scripts/python.exe -m pip install -r verification/requirements-data.txt
New-Item -ItemType Directory -Force target/eht-benchmark
curl.exe --fail --location --output 'target/eht-benchmark/sample_dump_SANE_a+0.94_MKS_0900.h5.part' 'https://dataverse.harvard.edu/api/access/datafile/12137142'
target/verification-python/Scripts/python.exe verification/check_snapshot.py 'target/eht-benchmark/sample_dump_SANE_a+0.94_MKS_0900.h5.part'
if ($LASTEXITCODE -ne 0) { throw 'Snapshot verification failed' }
Move-Item -LiteralPath 'target/eht-benchmark/sample_dump_SANE_a+0.94_MKS_0900.h5.part' -Destination 'target/eht-benchmark/sample_dump_SANE_a+0.94_MKS_0900.h5'
target/verification-python/Scripts/python.exe verification/test_snapshot.py
```

Subsequent checks need no network:

```powershell
target/verification-python/Scripts/python.exe verification/check_snapshot.py
```

The validator checks both hashes, file size, actual header, coordinate and
primitive conventions, finite primitives, and positive density/internal energy.
The negative tests reject substituted times, spin, grid, coordinates and
primitive order. A complete physical validation remains separate.

## Independent polarized reference

The reference solver is [AFD-Illinois/ipole](https://github.com/AFD-Illinois/ipole),
pinned to commit `7f7a482cf91125aeeeb9c431485bba680e8941d7`. Its upstream
license and attribution remain in the downloaded repository. The build uses
`MODEL=iharm`, GCC `-O2` with OpenMP, GSL 2.8 and HDF5 1.14.6. It has been
prepared under the existing Ubuntu 26.04 amd64 WSL environment; the scripts
unpack pinned Ubuntu libraries locally and do not install system packages.

From the repository root in PowerShell:

```powershell
wsl -d Ubuntu -- bash verification/benchmarks/build_ipole.sh
wsl -d Ubuntu -- bash verification/benchmarks/run_ipole.sh
```

The local library paths are embedded in the executable. Rebuild after moving
the checkout. Build and run logs are in `target/eht-reference/`.

[benchmarks/eht-ipole.par](benchmarks/eht-ipole.par) sets the paper's 160×160
image, 160 microarcsecond field, 230 GHz frequency, M87* mass/distance,
camera at 10000 r_g and 163 degrees, mass unit 1.672×10²⁶ g, fixed ion/electron
temperature ratio three and magnetization cutoff one. The regenerated Stokes
image is `target/eht-benchmark/ipole-reference.h5`. This uses the pinned current
solver; it is not an archived image from the original 2023 runs.

## Regenerated reference result

[fixtures/eht-reference.json](fixtures/eht-reference.json) records the source,
input/configuration hashes, software versions and measured totals. The original configuration hash records CRLF bytes; the fixture also records the checked-in LF hash. Only line endings changed; parameter names and values are identical. The first
checked run produced these integrated Stokes values in Jy:

| I | Q | U | V |
| --- | --- | --- | --- |
| 0.47976118576344184 | -0.006700681644500638 | -0.002915943556236394 | 0.00310100947421721 |

The separately computed unpolarized flux was 0.5046674123064179 Jy. Net linear
and circular polarization were 1.5231865% and 0.6463652%. Multiply the first
four components of the HDF5 `pol` dataset by `header/scale` to obtain Jy per
pixel; the remaining component is not a Stokes intensity. The file records
EVPA zero at North. All Stokes pixels were finite, with positive intensity
and no polarization-cone violation in this run. A second run through the saved build/run workflow reproduced all Stokes
pixels bit-for-bit on this machine. Matching integrated totals alone would
not establish matching images or physical truth.

## Snapshot and local transfer checks

The optional benchmark kernels are now implemented separately from the
interactive prescribed-plasma renderer:

- `assets/shaders/snapshot.wesl` samples the validated MKS grid, reconstructs
  fluid/magnetic four-vectors, and rotates them to the renderer's +Y spin frame.
  Radial ghosts copy edge cells, polar ghosts rotate azimuth by pi, and
  azimuth is periodic, matching the pinned iharm implementation. Interpolate
  primitive velocities/fields before reconstruction; physical scalars are
  prepared at cell centers and interpolated separately. Density is cut at
  interpolated sigma >= 1. It reports the emission mask for 1 < r < 100 and
  the reference polar cut; callers must honor that mask. The upstream zero-field temperature-floor behavior is
  retained, rather than replacing its arithmetic with an algebraic fixed-ratio
  simplification.
  Queries on the polar coordinate axis are rejected, where azimuth and the
  native vector basis are undefined; this lies inside the reference polar cut.
- `assets/shaders/thermal.wesl` implements the pinned Dexter thermal emission
  and conversion fits, Shcherbakov rotation, polarized Kirchhoff absorption,
  and the 0.99 polarization cap. Its interpolated GSL Bessel-ratio table and
  cold asymptotic branch avoid binary32 underflow. The source attribution and
  BSD license are retained in `assets/shaders/ipole-LICENSE.txt`.
- `assets/shaders/polarized_transfer.wesl` solves the full constant-cell
  four-Stokes affine system using a scaled matrix exponential, including
  polarized absorption and noncommuting Faraday terms. It rejects nonfinite,
  negative-length, nonpassive-absorption and oversized cells. A dimensionless
  matrix-norm bound above 8192 requires subdivision. This numerical solver is
  not covered by the older exact scalar-absorption Lean transfer theorem.

Run from the repository root after building the pinned reference:

```powershell
target/verification-python/Scripts/python.exe -m unittest discover -s verification -p 'test_*.py'
target/verification-python/Scripts/python.exe verification/check_sampling.py prepare
wsl -d Ubuntu -- bash verification/benchmarks/sample_ipole.sh
target/verification-python/Scripts/python.exe verification/check_sampling.py compare
target/verification-python/Scripts/python.exe verification/check_thermal.py prepare
wsl -d Ubuntu -- bash verification/benchmarks/sample_ipole.sh thermal
target/verification-python/Scripts/python.exe verification/check_thermal.py compare
target/verification-python/Scripts/python.exe verification/check_transfer.py
cargo test --offline --test rendering -- --include-ignored --nocapture --test-threads=1
```

The probe compiles the pinned solver's saved, unmodified source with a separate
entry point; it does not use the Python sampler to generate its expected values.
Generated grids, query sets, expected values, GPU outputs and detailed validation
JSON stay under `target/eht-benchmark/`. The grid payloads total about 235 MB.
The three storage bindings each fit WebGPU's default 128 MiB limit.

Local measurements on 2026-11-04:

| Check | Cases | Largest measured error |
| --- | ---: | ---: |
| CPU sampling vs direct ipole | 274 | 8.90e-14 scaled component error |
| GPU velocity / magnetic vector | 274 | 2.03e-6 / 8.16e-7 scaled component error |
| GPU physical scalars | 274 | 1.22e-5 scaled component error |
| GPU thermal emission / absorption / Faraday | 292 | 6.32e-6 / 9.94e-6 / 2.91e-6 family-scaled error |
| GPU full polarized cell | 128 | 6.38e-6 scaled component error |

Sampling/cell component errors use `abs(actual-reference)/max(1,abs(reference))`.
Coefficient errors divide by the largest absolute reference component in each
emission, absorption or Faraday family, with a 1e-20 absolute floor in the stated
physical units. That floor matters: the reference's polarization-cap norm
itself underflows for four test sources with intensity below 1e-140. These
tests do not claim relative accuracy of such negligible values. The independent
cell ODE reference was refined from 4096 to 8192 binary64 RK4 steps; its maximum
change was 1.61e-10. Exact zero-opacity, Faraday-rotation and thermal-equilibrium
cases check that reference separately.

Thermal coefficients use the fixed benchmark mass/length and 230 GHz observer.
For fluid-frame frequency nu and g = 230 GHz / nu, emission is
`L_unit * g^3 * j_nu`, absorption is `L_unit * alpha_nu`, and rotation/conversion
is `L_unit * rho_nu`. The cell distance must therefore be fluid-frame proper
path length in r_g. Transporting a ray in affine distance requires the local
fluid photon-energy factor; these quantities cannot be substituted directly
for the illustrative shader's arbitrary-unit coefficients. The supported
thermal domain is explicit in the shader (Theta_e in [0.001,1000], frequency
in [1e8,1e20] Hz, nonnegative bounded density/field, and pitch cosine in [-1,1]).
The extended frequency range is exercised by 27 additional direct-fit cases
(319 total) and is needed by highly redshifted near-horizon rays.

`BlackHole/SnapshotChart.lean` adds exact-real chart radius/ell identities,
the MKS polar derivative/lower bound/monotonicity/range, and the eight-weight
trilinear formula, constant reproduction and convex bounds. These proofs do
not certify HDF5 parsing, ghost indexing, binary32 evaluation or texture/buffer
execution; the independent probes cover finite samples of those behaviors.

## Remaining renderer correspondence

The local kernels are now connected in `tests/image.wesl`, with a matched
camera, fluid-frame frequency/path length, screen/pitch/Stokes conventions,
and foreground matrix composition. The interactive renderer continues to use
its prescribed plasma. The benchmark is a separate hybrid CPU/GPU path.

## Full image benchmark (2026-11-04)

Build the pinned reference first, then run:

```powershell
wsl -d Ubuntu -- bash verification/benchmarks/sample_ipole.sh camera
wsl -d Ubuntu -- bash verification/benchmarks/sample_ipole.sh outer
wsl -d Ubuntu -- bash verification/benchmarks/run_ipole.sh refined
target/verification-python/Scripts/python.exe verification/check_image.py prepare
cargo test --offline --test rendering headless_snapshot_image -- --ignored --nocapture
target/verification-python/Scripts/python.exe verification/check_image.py compare
```

The last command records `target/eht-benchmark/image-comparison.json` and
**exits unsuccessfully while the requested numerical targets remain unmet**.
The GPU regression separately checks finite output and resolved rays; passing
that regression does not assert numerical accuracy. `prepare --stride 8` is
a 400-ray diagnostic. `--cell-fraction 0.25`, `0.125`, and `0.0625` reproduce
the full-image refinement sequence; the default is 0.0625.

The independent camera probe checks all 25600 future tangents, native positions
and tetrad vectors. The camera uses the reference's normal observer,
zero-angular-momentum centering and -0.01 horizontal pixel offset. A per-ray
Jones matrix accounts for finite-field-angle projection onto the fixed camera
axes. The saved North-EVPA convention negates camera Q and U.

`outer_ray.py` integrates the emission-free segment from the 10000 r_g camera
to 120 r_g in binary64 Cartesian Kerr coordinates. On this machine the 229-step
run had null residual 5.01e-10, screen-norm error 2.51e-11 and transversality
error 2.84e-14. Halving the outer step on 16 rays changed state components by
at most 1.07e-8. A separate, refined native-coordinate ipole probe agreed within
2.55e-6 r_g in position and 3.26e-8 in momentum/screen components. This outer
segment emits nothing because the reference emission domain ends at 100 r_g.
The source-hashed cache under `target/` avoids repeating the binary64 batch
when only the transfer cell fraction changes.

The GPU segment uses the shared Kerr metric/RK4 controller with an optional
time-gauged screen RHS, bounded screen resets and homogeneous momentum
rescaling. The frequency and affine/path-length calculations compensate for
the momentum scale. Horizon clearance limits use radial motion: limiting total
Cartesian speed over-restricts rays spiraling around a rotating hole. All RK
stage validity checks remain. Capture occurs at clearance <= 0.0001 r_g;
escape requires outward radial motion beyond 100 r_g. The benchmark's distant
camera and 21000 affine-length budget are separate from the original admitted
camera/proof domain. No whole-step event or global error enclosure is claimed.

The default production `advance_ray` retains ungauged transport. Its previous
physics checks and six-scene headless GPU smoke test were rerun successfully.
`RayConditioning.lean` proves eight exact-real lemmas for tangent/force scaling,
energy and affine/fluid-length compensation, gauge-rate time cancellation and
bivector invariance, and full-matrix foreground composition. These do not bound
the finite-precision controller or cell solver.

The baseline ipole step parameter was 0.01. The added
`eht-ipole-refined.par` uses 0.0025 and writes `ipole-reference-refined.h5`.
Its integrated (I,Q,U,V) is (0.4771235045, -0.0076510932, -0.0023100384,
0.0031840019) Jy. Baseline-to-refined I changes by 5.98% in image L2 norm;
the baseline is therefore unsuitable as a high-accuracy truth image. The
refined reference also still needs convergence assessment.

All three full GPU images resolved 25600 rays: 990 captured, 24610 escaped,
and no exhausted/failed rays. At cell fraction 0.0625, integrated Stokes were
(0.4767574909, -0.0076398941, -0.0022573610, 0.0031861329) Jy. Total I differs
from the refined reference by about 0.077%; component L2 errors, divided by
reference I's L2 norm, are (0.688%, 0.216%, 0.285%, 0.0666%). These totals do
not establish pixel agreement: maximum I error is 2.64% of the fixed reference
peak, and the maximum relative I error above the chosen floor is about 44%.

The successive GPU I L2 changes are 0.126% and 0.180%; refinement has not
established convergence. The finest run's maximum normalized null residual is
1.23e-4, larger than in the coarser runs. Further work must separate transfer
quadrature from geodesic roundoff, refine the independent reference, and close
the error budgets. Simply reducing every step is insufficient. Recorded
measurements/provenance are in [fixtures/eht-image-checks.json](fixtures/eht-image-checks.json).
Cross-code agreement is empirical validation, not a universal proof of physical
accuracy. See [TARGETS.md](TARGETS.md) and [OBLIGATIONS.md](OBLIGATIONS.md).
