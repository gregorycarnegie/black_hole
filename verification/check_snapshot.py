"""Check the archived EHT snapshot's identity, header and primitive values."""

import hashlib
import json
import sys
from pathlib import Path

import h5py
import numpy as np

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "fixtures/eht-snapshot.json"


def read_header(snapshot):
    return {
        "time": float(snapshot["t"][()]),
        "spin": float(snapshot["header/geom/mks/a"][()]),
        "grid": [int(snapshot[f"header/n{i}"][()]) for i in (1, 2, 3)],
        "primitive_shape": list(snapshot["prims"].shape),
        "primitive_names": [x.decode("ascii") for x in snapshot["header/prim_names"][()]],
        "metric": snapshot["header/metric"][()].decode("ascii"),
        "adiabatic_index": float(snapshot["header/gam"][()]),
    }


def check_header(actual, expected):
    for key, value in expected.items():
        if actual.get(key) != value:
            raise ValueError(f"Snapshot {key}: expected {value!r}, got {actual.get(key)!r}")


def check_snapshot(path):
    expected = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if path.stat().st_size != expected["bytes"]:
        raise ValueError("Snapshot size does not match the archive")
    digests = {name: hashlib.new(name) for name in ("md5", "sha256")}
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            for digest in digests.values():
                digest.update(chunk)
    for name, digest in digests.items():
        if digest.hexdigest() != expected[name]:
            raise ValueError(f"Snapshot {name} does not match the archive")
    with h5py.File(path, "r") as snapshot:
        header = read_header(snapshot)
        check_header(header, expected["header"])
        for plane in snapshot["prims"]:
            if not np.isfinite(plane).all():
                raise ValueError("Nonfinite primitive values")
            if not (plane[..., :2] > 0).all():
                raise ValueError("Nonpositive density or internal energy")
        diagnostics = {
            "fail_flagged_cells": int(np.count_nonzero(snapshot["extras/fail"][...])),
            "fixup_flagged_cells": int(np.count_nonzero(snapshot["extras/fixup"][...])),
            "max_abs_divB_diagnostic": float(np.max(np.abs(snapshot["extras/divB"][...]))),
        }
    return {"path": str(path), "sha256": expected["sha256"], "header": header, "diagnostics": diagnostics}


if __name__ == "__main__":
    expected = json.loads(MANIFEST.read_text(encoding="utf-8"))
    path = Path(sys.argv[1]) if len(sys.argv) == 2 else ROOT.parent / "target/eht-benchmark" / expected["filename"]
    if len(sys.argv) > 2:
        sys.exit("usage: python check_snapshot.py [SNAPSHOT_H5]")
    print(json.dumps(check_snapshot(path), indent=2))
