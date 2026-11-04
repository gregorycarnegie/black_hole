"""Generate independent binary64 ODE references for full polarized cell transfer."""

import json
from pathlib import Path

import numpy as np

OUT = Path(__file__).resolve().parent.parent / "target/eht-benchmark"


def reference(cases, steps):
    j, a, r = cases[:, 0], cases[:, 1], cases[:, 2, :3]
    k = np.zeros((len(cases), 4, 4))
    k[:, range(4), range(4)] = a[:, :1]
    k[:, 0, 1:], k[:, 1:, 0] = a[:, 1:], a[:, 1:]
    k[:, 1, 2], k[:, 2, 1] = r[:, 2], -r[:, 2]
    k[:, 2, 3], k[:, 3, 2] = r[:, 0], -r[:, 0]
    k[:, 3, 1], k[:, 1, 3] = r[:, 1], -r[:, 1]
    h = cases[:, 2, 3, None] / steps
    value = cases[:, 3].copy()
    rhs = lambda s: j - np.einsum("nij,nj->ni", k, s)
    for _ in range(steps):
        b1 = rhs(value)
        b2 = rhs(value + h * b1 / 2)
        b3 = rhs(value + h * b2 / 2)
        b4 = rhs(value + h * b3)
        value += h / 6 * (b1 + 2*b2 + 2*b3 + b4)
    return value


def prepare():
    rng = np.random.default_rng(230)
    count = 128
    cases = np.zeros((count, 4, 4))
    for field in (0, 1, 3):
        intensity = 10**rng.uniform(-4, 1, count)
        direction = rng.normal(size=(count, 3))
        direction /= np.linalg.norm(direction, axis=1)[:, None]
        cases[:, field, 0] = intensity
        cases[:, field, 1:] = (intensity * rng.uniform(0, 0.8, count))[:, None] * direction
    cases[:, 2, :3] = rng.uniform(-15, 15, (count, 3))
    cases[:, 2, 3] = rng.uniform(0.01, 1, count)
    # Zero opacity, dichroism without Faraday, pure Faraday, and thermal equilibrium.
    cases[0, 1:3] = 0
    cases[0, 2, 3] = 1
    cases[1, 2] = [0, 0, 0, 1]
    cases[2, :2] = 0
    cases[2, 2] = [0, 0, 30, 1]
    cases[3, 1] = [100, 30, 20, -10]
    cases[3, 0] = 0.3 * cases[3, 1]
    cases[3, 2] = [0, 0, 0, 1]
    # References use the exact binary32 inputs uploaded to the GPU.
    cases = cases.astype("<f4").astype(np.float64)
    coarse, fine = reference(cases, 4096), reference(cases, 8192)
    error = float(np.max(np.abs(coarse - fine)))
    if error > 1e-8:
        raise ValueError(f"ODE reference did not converge: {error}")
    np.testing.assert_allclose(fine[0], cases[0, 3] + cases[0, 0], atol=1e-11, rtol=0)
    angle = 30
    initial = cases[2, 3]
    rotated = [initial[0], np.cos(angle)*initial[1]-np.sin(angle)*initial[2], np.sin(angle)*initial[1]+np.cos(angle)*initial[2], initial[3]]
    np.testing.assert_allclose(fine[2], rotated, atol=1e-9, rtol=0)
    np.testing.assert_allclose(fine[3], [0.3, 0, 0, 0], atol=2e-8, rtol=0)
    if np.any(np.linalg.norm(fine[:, 1:], axis=1) > fine[:, 0] + 1e-10):
        raise ValueError("Reference left the physical Stokes cone")
    OUT.mkdir(parents=True, exist_ok=True)
    cases.astype("<f4").tofile(OUT / "transfer-cases.f32")
    fine.astype("<f4").tofile(OUT / "transfer-expected.f32")
    report = {"cases": count, "reference": "binary64 RK4 ODE, 4096/8192 steps", "max_refinement_difference": error, "checks": ["zero opacity exact solution", "pure Faraday exact rotation", "thermal equilibrium", "Stokes cone", "polarized absorption and noncommuting Faraday terms"]}
    (OUT / "transfer-validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    prepare()
