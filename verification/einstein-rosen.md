# Einstein–Rosen bridge

The selectable view implements constant-Kruskal-time **equatorial spatial embeddings** of Schwarzschild spacetime, with G = c = M = 1 and r_s = 2. Press W twice from the black-hole view to select it. The separate [Ellis mode](ellis.md) ray traces a traversable wormhole.

Sources:

- Einstein & Rosen (1935), [The Particle Problem in the General Theory of Relativity](https://doi.org/10.1103/PhysRev.48.73), for the original two-sheet construction.
- Collas & Klein (2012), [Embeddings and time evolution of the Schwarzschild wormhole](https://arxiv.org/abs/1107.4871), Eqs. (3), (5), (21), (22), (24), for the implemented Kruskal slices and embedding slopes.
- Fuller & Wheeler (1962), [Causality and Multiply Connected Space-Time](https://doi.org/10.1103/PhysRev.128.919), for nontraversability.

Writing R = r/r_s, the numerical implementation in `src/einstein_rosen.rs` solves

```
(R - 1) exp(R) = u² - v²
dr/du = 2 r_s u / (R exp(R))
dz/du = 2 r_s sqrt(exp(R) - v²) / (R exp(R))
```

It integrates z from u = 0 using composite Simpson quadrature, then reflects z to produce the second sheet. The surface is `(r cos φ, z, r sin φ)`. Colors identify sheets; the embedding axis is auxiliary, not a traversable spatial tunnel. At v = 0 this reduces to the two signed Flamm paraboloids, z² = 4 r_s (r - r_s).

The display accepts |v| <= 0.95 and samples 0 <= u <= 32. On this domain [0, 8] brackets the unique dimensionless radius. It performs 56 bisection iterations per sample and uses 128 quadrature panels with u distributed quadratically near the throat. The singular slices |v| = 1 and post-pinch geometry are outside this implementation. Playback advances v by 0.2 per elapsed application second, pauses at the upper boundary, and never represents a physical observer trajectory.

`BlackHole/EinsteinRosen.lean` proves, over exact reals:

- The Kruskal radius relation has positive derivative away from R = 0 and is strictly increasing for R >= 0, establishing uniqueness of inversion.
- The embedding radicand is positive for R >= 0 and v² < 1.
- The implemented slopes satisfy `(dr/du)² + (dz/du)² = 4 r_s² / (R exp(R))`, matching the induced spatial metric.
- At v = 0 the throat has r = r_s and both exteriors have r >= r_s; increasing |v| contracts the throat.
- Nonpositive spacetime norm, a positive conformal factor, nonnegative angular norm, and future-directed time imply |du/dλ| <= dv/dλ. The future cone endpoint inequality excludes travel from exterior I to III; a curve theorem proves the obstruction for differentiable curves throughout an interval. Reflection u -> -u gives the other direction.

These proofs check the manually transcribed real formulas. They do **not** certify floating-point bisection, quadrature error, tessellation, Bevy rendering, or the full global spacetime construction. The metric-to-cone theorem assumes a nonnegative angular contribution; the curve theorem assumes differentiability throughout its parameter interval. No new proof of the Einstein field equations is claimed.

Rust checks the radius residual and induced metric at sampled points on five slices, time-reversal symmetry, strict throat contraction, invalid inputs, and the analytic v = 0 profile. It also compares heights against four-times-finer quadrature, with a 2e-5 r_g tolerance on those five slices; this is a regression tolerance, not a uniform error certificate. UI tests cover clamping, pause/reset, and camera restoration. An optional GPU test renders the complete scene, checks the controls and switching, and writes `target/bridge-smoke.png`.

Run from the repository root:

```sh
cargo test einstein_rosen
cargo test bridge::tests
cargo test bridge_scene_renders_and_switches_back -- --ignored --nocapture
cd verification
lake build BlackHole.EinsteinRosen
lake env leanchecker BlackHole.EinsteinRosen
```

The module is imported by `BlackHole.lean`, so the existing complete build, axiom audit, and independent replay also include these declarations.
