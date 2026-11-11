"""Prepare snapshot sampling inputs, then compare with the standalone Zig solver.

Run with 'prepare', sample_ipole.sh, then 'compare'. GPU buffers are only
exported after the independent double-precision comparison passes.
"""

import json
import sys
from pathlib import Path

import numpy as np
from eht_snapshot import (
    L_UNIT,
    Snapshot,
    default_path,
    jacobian,
    native_metric,
    theta,
    to_native,
    to_world,
)

OUT = Path(__file__).resolve().parent.parent / "target/eht-benchmark"


def prepare():
    snapshot = Snapshot(default_path())
    rng = np.random.default_rng(9375)
    fractional = rng.uniform(0.05, 0.95, (256, 3)) * snapshot.grid
    # Exercise both poles' ghost cells, radial extension, and the azimuth seam.
    edges = np.array(np.meshgrid([0.05, snapshot.grid[0] - 0.05], [0.05, 64, snapshot.grid[1] - 0.05], [0, 0.05, snapshot.grid[2] - 0.05], indexing="ij")).reshape(3, -1).T
    x = snapshot.start + np.concatenate((fractional, edges)) * snapshot.dx
    # Oracle and GPU queries start at the very same binary32 world position.
    pos = to_world(x, snapshot.spin, snapshot.hslope).astype("<f4")
    x = to_native(pos, snapshot.spin, snapshot.hslope)
    x.astype("<f8").tofile(OUT / "sample-queries.f64")
    np.column_stack((pos, np.zeros(len(pos)))).astype("<f4").tofile(OUT / "sample-positions.f32")
    print(f"Prepared {len(x)} independent queries")


def compare():
    snapshot = Snapshot(default_path())
    x = np.fromfile(OUT / "sample-queries.f64", dtype="<f8").reshape(-1, 3)
    ref = np.fromfile(OUT / "sample-ipole.f64", dtype="<f8").reshape(-1, 40)
    if len(ref) != len(x):
        raise ValueError("Incomplete independent oracle output")
    p, u, b, physical = snapshot.sample(x)
    g, j = native_metric(x, snapshot.spin, snapshot.hslope), jacobian(x, snapshot.spin, snapshot.hslope)
    r, th = np.exp(x[:, 0]), theta(x[:, 1], snapshot.hslope)
    emitting = (r > 1) & (r < 100) & (th > 0.0174) & (th < np.pi - 0.0174)
    actual = np.column_stack((p, u, b, physical, g.reshape(-1, 16), to_world(x, snapshot.spin, snapshot.hslope), emitting))
    if not np.isfinite(actual).all() or not np.isfinite(ref).all():
        raise ValueError("Nonfinite sample")
    error = np.max(np.abs(actual - ref) / np.maximum(1, np.abs(ref)), axis=0)
    np.testing.assert_allclose(actual, ref, rtol=2e-9, atol=2e-10)
    uw, bw = np.einsum("nij,nj->ni", j, u), np.einsum("nij,nj->ni", j, b)
    pos = to_world(x, snapshot.spin, snapshot.hslope)
    a = np.array([0, snapshot.spin, 0])
    ell = (r[:, None] * pos - np.cross(a, pos) + (snapshot.spin * pos[:, 1] / r)[:, None] * a) / (r**2 + snapshot.spin**2)[:, None]
    ell = np.column_stack((np.ones(len(x)), ell))
    h = r**3 / (r**4 + (snapshot.spin * pos[:, 1])**2)
    gw = np.diag([-1., 1, 1, 1]) + 2 * h[:, None, None] * ell[:, :, None] * ell[:, None, :]
    pullback = np.einsum("nji,njk,nkl->nil", j, gw, j)
    np.testing.assert_allclose(pullback, g, rtol=2e-9, atol=3e-9)
    np.testing.assert_allclose(np.einsum("ni,nij,nj->n", uw, gw, uw), -1, rtol=0, atol=5e-11)
    np.testing.assert_allclose(np.einsum("ni,nij,nj->n", uw, gw, bw), 0, rtol=0, atol=5e-11)
    # Three vec4 arrays each fit WebGPU's default 128 MiB storage binding limit.
    for name, values in (("primitives0", snapshot.primitives[..., :4]), ("primitives1", snapshot.primitives[..., 4:]), ("physical", snapshot.physical)):
        values.astype("<f4").tofile(OUT / f"sample-{name}.f32")
    header = np.zeros((5, 4), dtype="<f4")
    header[0, :3], header[1, :3], header[2, :3] = snapshot.start, snapshot.dx, snapshot.grid
    header[3] = [snapshot.spin, snapshot.hslope, 1, 100]
    header[4] = [L_UNIT, 1, 0.0174, 0]
    header.tofile(OUT / "sample-header.f32")
    # Output: world u, world b, physical (ne,Thetae,Bgauss,sigma), native x+mask.
    np.column_stack((uw, bw, physical, x, emitting)).astype("<f4").tofile(OUT / "sample-expected.f32")
    report = {"samples": len(x), "snapshot_sha256": snapshot.identity["sha256"], "reference_solver": "standalone Zig", "convention_source_ipole_commit": "7f7a482cf91125aeeeb9c431485bba680e8941d7", "max_component_scaled_error": float(np.max(error)), "electron_density_nonzero_samples": int(np.count_nonzero(physical[:, 0])), "radiating_samples": int(np.count_nonzero(emitting)), "length_unit_cm": L_UNIT, "checks": ["8 interpolated primitives", "native velocity and magnetic four-vectors", "4 physical scalars and sigma cut", "native metric", "Cartesian positions and metric pullback", "timelike normalization and magnetic orthogonality", "radiating-region mask"]}
    (OUT / "sampling-validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    if sys.argv[1:] == ["prepare"]:
        prepare()
    elif sys.argv[1:] == ["compare"]:
        compare()
    else:
        sys.exit("usage: python check_sampling.py prepare|compare")
