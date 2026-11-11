"""Prepare matched camera rays and compare the GPU image to the Zig reference."""

import argparse
import hashlib
import inspect
import json
from pathlib import Path

import numpy as np
from check_snapshot import check_snapshot
from eht_snapshot import L_UNIT, default_path, jacobian, native_metric, theta, to_world
from outer_ray import trace

OUT = Path(__file__).resolve().parent.parent / "target/eht-benchmark"


def read_reference(filename):
    """Require a complete native reference, never a sparse diagnostic image."""
    meta = json.loads((OUT / (filename + ".json")).read_text())
    if meta.get("shape") != [160, 160, 4] or meta.get("stride") != 1:
        raise ValueError("Zig reference must contain all 25600 pixels")
    if meta.get("snapshot_sha256") != "c2d1dfdc8c92320ec77d22953f55c2b5d71b685496f5199c73a1280f20a0d537":
        raise ValueError("Zig reference snapshot identity mismatch")
    expected_eps = 0.0025 if filename == "zig-reference-refined.f64" else 0.01
    if meta.get("eps") != expected_eps:
        raise ValueError("Zig reference step parameter mismatch")
    values = np.fromfile(OUT / filename, dtype="<f8")
    if values.size != 25600 * 4 or not np.isfinite(values).all():
        raise ValueError("Incomplete or nonfinite Zig reference")
    return values.reshape(25600, 4)


def camera():
    lo, hi = 0., 1.
    for _ in range(56):
        mid = (lo + hi) / 2
        if theta(mid, 0.3) < np.deg2rad(163): lo = mid
        else: hi = mid
    x = np.array([np.log(10000), (lo+hi)/2, 0.])
    g = native_metric(x, 0.9375, 0.3)
    inv = np.linalg.inv(g)
    frame = np.array([inv @ [-1., 0, 0, 0], np.ones(4), [0, 0, 1., 0], inv @ [1., 1, 0, 0]])
    for target, others in [(0, []), (3, [0, 0]), (2, [0, 3, 0, 3]), (1, [0, 2, 3, 0, 2, 3])]:
        for other in others:
            frame[target] -= frame[other] * ((frame[target] @ g @ frame[other]) / (frame[other] @ g @ frame[other]))
        frame[target] /= np.sqrt(abs(frame[target] @ g @ frame[target]))
    if np.linalg.det(frame) < 0: frame[1] *= -1
    i, j = np.meshgrid(np.arange(160), np.arange(160), indexing="ij")
    fov = 160 * (16.9e6 * 3.085678e18) / L_UNIT / 2.06265e11 / 10000
    tx, ty = ((i.ravel()+0.5-0.01)/160-0.5)*fov, ((j.ravel()+0.5)/160-0.5)*fov
    direction = (tx[:, None]*frame[1]+ty[:, None]*frame[2]+frame[3])/np.sqrt(1+tx*tx+ty*ty)[:, None]
    future = frame[0] + direction
    f1 = frame[1] - direction * (direction @ g @ frame[1])[:, None]
    f1 /= np.sqrt(np.einsum("ni,ij,nj->n", f1, g, f1))[:, None]
    f2 = frame[2] - direction * (direction @ g @ frame[2])[:, None]
    f2 -= f1 * np.einsum("ni,ij,nj->n", f2, g, f1)[:, None]
    f2 /= np.sqrt(np.einsum("ni,ij,nj->n", f2, g, f2))[:, None]
    np.testing.assert_allclose(np.einsum("ni,ij,nj->n", future, g, future), 0, atol=2e-15)
    oracle = np.fromfile(OUT / "camera-ipole.f64", dtype="<f8").reshape(25600, 24)
    np.testing.assert_allclose(oracle[:, 1:4], np.broadcast_to(x, (25600, 3)), rtol=0, atol=1e-10)
    np.testing.assert_allclose(oracle[:, 4:8], future, rtol=2e-9, atol=2e-12)
    np.testing.assert_allclose(oracle[:, 8:].reshape(-1, 4, 4), np.broadcast_to(frame, (25600, 4, 4)), rtol=2e-9, atol=2e-12)
    transform = jacobian(x, 0.9375, 0.3)
    world_g = np.linalg.inv(transform).T @ g @ np.linalg.inv(transform)
    p = -(future @ g) @ np.linalg.inv(transform)
    screen = f1 @ transform.T
    # Jones map to the fixed camera axes includes finite-field-angle projection.
    jones = np.column_stack((f1 @ g @ frame[1], f2 @ g @ frame[1], f1 @ g @ frame[2], f2 @ g @ frame[2]))
    seeds = np.zeros((25600, 4, 4), dtype="<f8")
    seeds[:, 0, :3] = to_world(x, 0.9375, 0.3)
    seeds[:, 1], seeds[:, 2], seeds[:, 3] = p, screen, jones
    np.testing.assert_allclose(np.einsum("ni,ij,nj->n", screen, world_g, screen), 1, atol=3e-15)
    return seeds


def check_outer(seeds):
    oracle=np.fromfile(OUT/"outer-ipole.f64",dtype="<f8").reshape(16,12)
    x=oracle[:,1:4]
    transform=jacobian(x,0.9375,0.3)
    inverse=np.linalg.inv(transform)
    g=native_metric(x,0.9375,0.3)
    p=-np.einsum("ni,nij,njk->nk",oracle[:,4:8],g,inverse)
    k=np.einsum("nij,nj->ni",transform,oracle[:,4:8])
    f=np.einsum("nij,nj->ni",transform,oracle[:,8:12])
    f-=k*(f[:,0]/k[:,0])[:,None]
    selected=np.linspace(0,25599,16,dtype=int)
    expected=np.column_stack((to_world(x,0.9375,0.3),p,f))
    actual=np.column_stack((seeds[selected,0,:3],seeds[selected,1],seeds[selected,2]))
    np.testing.assert_allclose(actual[:,:3],expected[:,:3],rtol=0,atol=1e-5)
    np.testing.assert_allclose(actual[:,3:],expected[:,3:],rtol=0,atol=3e-7)
    return {"position":float(np.max(np.abs(actual[:,:3]-expected[:,:3]))),"momentum_screen":float(np.max(np.abs(actual[:,3:]-expected[:,3:])))}


def prepare(args):
    identity = check_snapshot(default_path())
    seeds = camera()
    if not 0 < args.outer_fraction <= 0.02: raise ValueError("Outer fraction must be in (0,0.02]")
    tag=hashlib.sha256(inspect.getsource(camera).encode()+Path(__file__).with_name("outer_ray.py").read_bytes()).hexdigest()[:12]
    cache=OUT/f"image-outer-{args.outer_fraction}-{tag}.npz"
    if cache.exists():
        with np.load(cache) as data:
            seeds=data["seeds"]
            outer=json.loads(str(data["report"]))
    else:
        selected=np.linspace(0,len(seeds)-1,16,dtype=int)
        coarse,outer=trace(seeds,args.outer_fraction)
        fine,_=trace(seeds[selected],args.outer_fraction/2)
        delta=np.abs(coarse[selected]-fine)
        error=max(np.max(delta[:,0,:3]),np.max(delta[:,1:3,:]))
        if error>1e-5: raise ValueError(f"Outer RK4 refinement failed: {error}")
        outer["max_refinement_difference"]=float(error)
        seeds=coarse
        np.savez(cache,seeds=seeds,report=json.dumps(outer))
    outer["independent_zig_max_error"]=check_outer(seeds)
    if args.stride < 1 or args.stride > 160 or not 0 < args.cell_fraction <= 1:
        raise ValueError("Require stride in [1,160] and cell fraction in (0,1]")
    i, j = np.meshgrid(np.arange(0,160,args.stride), np.arange(0,160,args.stride), indexing="ij")
    indices = (160*i+j).ravel()
    seeds[indices].astype("<f4").tofile(OUT / "image-seeds.f32")
    scale = (160 / 2.06265e11 / 160)**2 / 1e-23
    np.array([args.cell_fraction, 50000, len(indices), scale], dtype="<f4").tofile(OUT / "image-settings.f32")
    meta = {"snapshot_sha256": identity["sha256"], "indices": indices.tolist(), "shape": list(i.shape), "cell_fraction": args.cell_fraction, "camera_probe": "all 25600 camera positions, future tangents and tetrad vectors matched standalone Zig reference", "observer_frequency_hz": 230e9, "Jy_per_CGS_intensity": scale}
    meta["outer_transport"]=outer
    meta["outer_fraction"]=args.outer_fraction
    (OUT / "image-input.json").write_text(json.dumps(meta, indent=2)+"\n", encoding="utf-8")
    print(f"Prepared {len(indices)} rays; cell fraction {args.cell_fraction}")


def compare():
    meta = json.loads((OUT / "image-input.json").read_text())
    values = np.fromfile(OUT / "image-gpu.f32", dtype="<f4").reshape(-1, 16)
    indices = meta["indices"]
    if len(values) != len(indices) or not np.isfinite(values).all():
        raise ValueError("Incomplete/nonfinite image output")
    status, counts = np.unique(values[:, 5].astype(int), return_counts=True)
    statuses = dict(zip(map(str, status), map(int, counts)))
    full_reference = read_reference("zig-reference-refined.f64")
    expected = full_reference[indices]
    baseline = read_reference("zig-reference.f64")[indices]
    actual = values[:, :4].astype(float)
    denominator = np.linalg.norm(expected[:, 0])
    error = actual-expected
    report = {"pixels": len(values), "cell_fraction": meta["cell_fraction"], "status_counts": statuses, "summed_stokes_Jy": actual.sum(axis=0).tolist(), "reference_summed_stokes_Jy": expected.sum(axis=0).tolist(), "component_l2_error_over_reference_I_l2": (np.linalg.norm(error,axis=0)/denominator).tolist(), "max_absolute_error_Jy": np.abs(error).max(axis=0).tolist(), "max_steps": int(values[:,4].max()), "max_null_residual": float(values[:,6].max()), "max_affine_length": float(values[:,7].max()), "complete_image": len(values)==25600, "scope": "empirical cross-code comparison; no universal accuracy claim"}
    reference_intensity=float(full_reference[:,0].max())
    bright=expected[:,0]>1e-6*reference_intensity
    relative_I=float(np.max(np.abs(error[bright,0])/expected[bright,0]))
    max_normalized=np.abs(error).max(axis=0)/reference_intensity
    report.update({"reference_file":"zig-reference-refined.f64", "reference_eps":0.0025,
        "fixed_reference_intensity_Jy":reference_intensity,
        "max_component_error_over_fixed_reference_I":max_normalized.tolist(),
        "max_relative_I_error_above_floor":relative_I,
        "requested_numerical_targets_met":bool(np.all(max_normalized<=1e-6) and relative_I<=1e-4),
        "zig_baseline_to_refined_l2_change_over_I_l2":(np.linalg.norm(expected-baseline,axis=0)/denominator).tolist(),
        "camera_and_outer_transport":meta["outer_transport"]})
    (OUT / "image-comparison.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))
    if not np.isin(values[:,5], [1,2]).all():
        raise ValueError("Image contains unresolved or failed rays; inspect status_counts")
    if not report["requested_numerical_targets_met"]:
        raise SystemExit("Requested numerical accuracy targets are not met; see image-comparison.json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare", "compare"])
    parser.add_argument("--stride", type=int, default=1)
    parser.add_argument("--cell-fraction", type=float, default=0.0625)
    parser.add_argument("--outer-fraction", type=float, default=0.02)
    args = parser.parse_args()
    prepare(args) if args.action == "prepare" else compare()
