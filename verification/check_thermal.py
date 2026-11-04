"""Prepare physical coefficient queries and package pinned ipole references."""

import json
import sys
from pathlib import Path

import numpy as np

OUT = Path(__file__).resolve().parent.parent / "target/eht-benchmark"


def prepare():
    OUT.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(2016)
    q = np.column_stack((10**rng.uniform(1, 7, 256), 10**rng.uniform(-3, 3, 256), 10**rng.uniform(-2, 2, 256), 10**rng.uniform(10, 13, 256), rng.uniform(-1, 1, 256)))
    edges = np.array([[1e4, t, b, 230e9, mu] for t in (0.001, 0.0014, 0.0015, 0.002, 1., 1000.) for b in (0, 10) for mu in (-1., 0., 1.)])
    high_frequency = np.array([[1e4, t, 10, nu, mu] for t in (0.001, 1., 100.) for nu in (1e15, 1e18, 1e20) for mu in (-1., 0., 1.)])
    q = np.concatenate((q, edges, high_frequency)).astype("<f4").astype("<f8")
    q.tofile(OUT / "thermal-queries.f64")
    gpu = np.zeros((len(q), 2, 4), dtype="<f4")
    gpu[:, 0, :3], gpu[:, 1, :2] = q[:, :3], q[:, 3:]
    gpu.tofile(OUT / "thermal-cases.f32")
    print(f"Prepared {len(q)} thermal coefficient queries")


def compare():
    q = np.fromfile(OUT / "thermal-queries.f64", dtype="<f8").reshape(-1, 5)
    ref = np.fromfile(OUT / "thermal-ipole.f64", dtype="<f8").reshape(-1, 12)
    if len(q) != len(ref) or not np.isfinite(ref).all():
        raise ValueError("Incomplete or nonfinite thermal reference")
    normal_emission = ref[:, 0] > 1e-20
    if np.any(np.linalg.norm(ref[normal_emission, 1:4], axis=1) > ref[normal_emission, 0]*(0.99+1e-12)):
        raise ValueError("Invalid source polarization")
    normal_absorption = ref[:, 4] > 1e-20
    if np.any(np.linalg.norm(ref[normal_absorption, 5:8], axis=1) > ref[normal_absorption, 4]*(0.99+1e-12)):
        raise ValueError("Invalid polarized absorption")
    if not np.isfinite(ref.astype("<f4")).all():
        raise ValueError("Reference cannot be represented in binary32")
    ref.astype("<f4").tofile(OUT / "thermal-expected.f32")
    report = {"cases": len(q), "ipole_commit": "7f7a482cf91125aeeeb9c431485bba680e8941d7", "distribution": "Dexter 2016 thermal emissivity/conversion, Shcherbakov rotation", "units": "observer-scaled CGS intensity per r_g of fluid path; absorption and Faraday per r_g", "observer_frequency_hz": 230e9, "checks": ["finite coefficients", "0.99 emission/absorption cap above the 1e-20 intensity/opacity floor", "zero field", "parallel/antiparallel field", "temperature floor", "GSL cold underflow convention"]}
    (OUT / "thermal-validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    if sys.argv[1:] == ["prepare"]: prepare()
    elif sys.argv[1:] == ["compare"]: compare()
    else: sys.exit("usage: python check_thermal.py prepare|compare")
