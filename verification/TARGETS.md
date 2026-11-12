# Accuracy targets

The user delegated the choice of verification targets and requested maximum
physical accuracy. These are the reference and acceptance targets for the
remaining proofs. They are requirements to establish, not claims that the
current renderer satisfies them.

## Geometry and rays

Use an isolated, stationary Kerr black hole as the primary exact reference,
with G=c=M=1, arbitrary spin orientation and |a|≤0.999. Include the exact
Schwarzschild limit, circular photon orbits, near-critical scattering,
prograde/retrograde circular timelike orbits, and the analytic ISCO results.
The frozen binary superposition has already failed the vacuum equations;
certifying an exact binary requires an evolved relativistic metric.

Cover the camera's current Euclidean radius range [1.6,160] wherever its
initial metric is valid and its Kerr-radius horizon clearance is at least
0.002. Follow each ray while it remains within radius 1632, all four covariant
momentum components have magnitude at most 10000, and affine length is at most
10000. Normalize the initial energy measured by the Eulerian observer to one.
The outer radius includes one maximum 32-unit spatial step beyond the
renderer’s current escape sphere at 1600. Paths leaving these verification
bounds require an explicit unresolved result or another bound.

Choose a position error target of 10⁻⁶ max(1,|x|∞), momentum error of
10⁻⁶ max(1,|p|∞), and escaping direction error of 10⁻⁶ radians. Bound screen
norm/transversality errors and redshift relative error by 10⁻⁶. These are
numerical verification targets chosen for this project, not thresholds taken
from an observational paper. Binary32, fixed iteration caps and the local step-doubling
acceptance estimate have not been proved to meet them.

Capture and escape need certified bounds on the corresponding whole step,
including stages, crossing location and event ordering. Classify a ray only
when its error enclosure lies entirely on the appropriate side of an event
boundary. Keep critical rays, exhausted budgets and inconclusive enclosures
unresolved. A universal finite termination guarantee for all critical rays
is not a suitable requirement.

## Radiation and physical reference

Use the analytic constant-coefficient polarized-transfer tests, relativistic
thin-disk tests and shared GRMHD snapshot comparisons in
[Prather et al. (2023), *Comparison of Polarized Radiative Transfer Codes Used
by the EHT Collaboration*](https://knowledge.lancashire.ac.uk/id/eprint/46103/1/Prather_2023_ApJ_950_35.pdf)
as the reference suite. Sections 3.1–3.3 distinguish analytic checks from
model-to-model comparisons. Use their M87* snapshot configuration at 230 GHz
as the first physical comparison target; the project's current default
frequency is also 230 GHz. The published configuration specifies mass,
distance, viewing geometry and fluid scaling; its snapshot must be obtained
and its conventions reproduced before claiming agreement.

Target each invariant Stokes component's absolute numerical error at
10⁻⁶ of a fixed reference intensity; additionally target relative intensity
error at 10⁻⁴ where the reference exceeds that floor. Define the reference
intensity from the chosen benchmark before evaluating errors, not from each
computed pixel. Verify the transfer and geodesic errors separately and combine
their budgets. Brightness, polarization fractions and image differences from
a shared snapshot assess consistency; they do not prove the physical truth
of a prescribed plasma model or calibrate the current arbitrary-unit recipes.

### Snapshot benchmark inputs

Section 3.3 of the [reference paper](https://arxiv.org/abs/2303.12004) specifies:

| Quantity | Reference value |
| --- | --- |
| Fluid snapshot | iharm3D SANE, spin 0.9375, time 4500 GM/c³ |
| Grid | 288 × 128 × 128 |
| Black-hole mass / distance | 6.2 × 10⁹ solar masses / 16.9 Mpc |
| Frequency | 230 GHz |
| Camera | radius 10⁴ r_g, inclination 163°, azimuth 0° |
| Image | 160 × 160 pixels, 160 microarcseconds, width 44.17 r_g |
| Density mass unit | 1.672 × 10²⁶ g |
| Transfer | Thermal synchrotron, frozen fluid snapshot (fast light) |

The exact comparison input is now public in [Harvard Dataverse,
DOI 10.7910/DVN/XZECPF](https://doi.org/10.7910/DVN/XZECPF), version 1.2,
file 12137142, CC0-1.0. It was downloaded and checked against the archive's
MD5 and a recorded SHA-256 on 2026-11-03. Its actual header time is
4501.677840911209, while the paper uses the nominal dump time 4500. Its spin
and 288×128×128 grid match the benchmark. The exact metadata and hashes are
in [fixtures/eht-snapshot.json](fixtures/eht-snapshot.json); acquisition and
reference-solver commands are in [benchmark-data.md](benchmark-data.md).

Reproducing it also requires matching the electron prescription,
coefficient fits, coordinate/interpolation conventions and image orientation.
The reference camera lies outside this project's current admitted camera/ray
domain; the benchmark harness needs a separate domain and outer-boundary rule.
Obtaining this input does not calibrate the current prescribed plasma.

## Proof boundary

Local snapshot, physical-coefficient and full polarized-cell WESL kernels now
have independent sampled checks; [benchmark-data.md](benchmark-data.md) gives
their units, explicit domains, regeneration commands and measurements. These
components now run in a full 160x160 hybrid snapshot benchmark. The recorded
image comparison fails the numerical targets above; finite local tests and
integrated-flux agreement do not replace trajectory, transfer or pixel bounds.

The [2026-11-11 accuracy/performance audit](accuracy-performance.md) records
fresh CUDA results, fixes for tiny-opacity rejection, a transfer optimization
with unchanged measured Stokes output, and the remaining reference/trajectory
limits. None of the numerical targets above were relaxed.

Do not turn requested accuracy into an axiom. N1–N4 still require a nonlinear
consistency proof, explicit derivative/Lipschitz bounds, arithmetic error
bounds and event separation. The former null-only controller failed a checked radial target. The current
position/momentum/screen step-doubling estimate rejects that example but is
not a certified error enclosure; higher-order and rounding terms still need bounds. The accuracy budget must include
roundoff, guard/branch effects, transfer approximation and the finite outer
boundary; reducing the step alone is insufficient.

Hardware/compiler correctness remains an external trust boundary. Empirical
reference data and model changes remain distinguishable from Lean theorems.
