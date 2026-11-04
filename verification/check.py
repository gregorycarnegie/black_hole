"""Build the large curvature proofs serially, audit axioms, replay the kernel."""

import os
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ENV = {**os.environ, "LEAN_NUM_THREADS": "1"}


def run(*arguments):
    start = time.monotonic()
    print("==> lake " + " ".join(arguments), flush=True)
    subprocess.run(["lake", *arguments], cwd=ROOT, env=ENV, check=True)
    print(f"<== done in {time.monotonic() - start:.0f}s", flush=True)


if __name__ == "__main__":
    # Concurrent curvature checks exhausted a 64 GB workstation.
    for module in (
        "KerrVacuumTime",
        "KerrVacuumSpatial11",
        "KerrVacuumSpatial12",
        "KerrVacuumSpatial13",
        "KerrVacuumSpatial22",
        "KerrVacuumSpatial23",
        "KerrVacuumSpatial33",
        "KerrVacuumMixed",
    ):
        run("--no-ansi", "build", f"BlackHole.{module}")
    run("--no-ansi", "build")
    run("env", "lean", "Audit.lean")
    run("env", "leanchecker", "-v", "BlackHole")
