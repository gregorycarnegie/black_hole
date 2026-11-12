# Accuracy without a blanket runtime cost (2026-11-11)

The numerical targets in `TARGETS.md` remain unchanged and unmet. This audit
uses freshly executed CUDA kernels, not the saved GPU image used in the Zig
migration report. Measurements are in
[fixtures/eht-accuracy-performance.json](fixtures/eht-accuracy-performance.json).

## Fixed during the audit

The original current-CUDA image run failed on 20809 of 25600 rays. Squaring
opacities around 1e-23 rounded their norm into the binary32 subnormal range,
so the passivity check rejected valid cells. Smaller transfer steps cannot
repair that coefficient check; repeated retries eventually stopped moving.

The check now normalizes before squaring and continues to reject genuinely
nonpassive input, including tiny nonpassive input. Thermal polarization is
capped before applying the exponentially small emissivity. Absorption is
formed from the intensity and that dimensionless polarization, avoiding
amplification of quantization in subnormal emission components.

All 25600 rays now finish: 990 captured and 24610 escaped, with no failed or
exhausted rays. New regressions cover tiny passive/nonpassive opacity; all
319 thermal cases also check the polarization cap after scaling.

The constant-cell exponential now uses eight Taylor terms instead of twelve.
Its existing scaling enforces ||hK|| <= 1/8, giving an exact-arithmetic
ninth-order remainder below 2.4e-14 before squaring. This is not a global
floating-point error proof. The complete 25600-pixel Stokes image was
bit-for-bit identical to the corrected twelve-term implementation.

CUDA-event timings on this RTX 4090, excluding uploads and downloads:

| Corrected transfer | Three kernel times (ms) | Median (ms) |
| --- | --- | --- |
| Twelve terms | 616.379, 604.999, 620.646 | 616.379 |
| Eight terms | 594.214, 597.949, 620.921 | 597.949 |

The median is about 3% lower, with overlapping timing ranges. This is a small
single-machine measurement, not a guaranteed speedup. Step tolerance, grid
fraction, iteration limits, and all accuracy acceptance targets were unchanged.
These fixes affect the snapshot benchmark and its local transfer tests; the
interactive prescribed-plasma renderer uses a separate transfer routine.

All 21 rendering tests (including GPU cases) and 42 compute tests pass.
The near-critical classification regression now requires zero wrong resolved
answers, replacing its stale requirement that a counterexample must occur.
The trajectory diagnostic still demonstrates failures; passing that diagnostic
does not mean that its trajectories meet the accuracy targets.

## Remaining limits and next experiments

- **The reference is not converged.** On 400 rays, reducing the Zig midpoint
  step from 0.0025 to 0.00125 changes intensity by 0.209% in L2 and by 0.257%
  of peak at the worst pixel. At 0.000625 a ray exceeds the 100000-step
  reference budget. First improve the offline Zig reference with a higher-order
  integrator and analytic MKS derivatives. That has no interactive frame cost
  and avoids treating an uncertain reference as exact truth.
- **Some production trajectories miss their targets.** The independently
  converged Schwarzschild test at impact 5.3 has position error 1.646e-3
  versus target 1.023e-4, and momentum error 1.500e-5 versus 1e-6. Impact 5.25
  also fails. A useful experiment is higher-order extrapolation from the
  coarse/fine RK4 results already computed by the controller: no additional
  force evaluations, but accuracy, stage/event guards and runtime still need
  measuring before adoption. Compensated accumulation or selective precision
  for sensitive rays are subsequent experiments, not established fixes.
- **The full image still fails.** Current intensity L2 discrepancy is 0.719%;
  worst intensity error is 2.75% of reference peak and worst relative intensity
  error above the floor is 24.3%. These are comparisons to an uncertain
  reference, not certified errors. After the reference is improved, separate
  path error from transfer quadrature and the discontinuous sigma/emission
  masks. Refine at detected difficult boundaries rather than reducing every
  ray's step uniformly, and retain unresolved results where required.

Final validation on 2026-11-12 passed Clippy with warnings denied, the standard
Rust test suite, all 21 rendering tests including GPU cases, and eight Python
tests. The passive-opacity regression includes 3e-23, which reproduces the
original upward-rounding rejection. The full image remains bit-identical to
the corrected twelve-term transfer result.

These CUDA changes have no new Lean correspondence or floating-point error
proof. No global error or whole-step event enclosure was added, and this work
does not claim that the target accuracy is achieved.
