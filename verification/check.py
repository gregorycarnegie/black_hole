"""Build the large curvature proofs serially, audit axioms, replay the kernel.

`--build` runs the build and axiom audit only, `--replay` only the independent
kernel replay of an existing build. With neither flag both phases run. CI uses
separate jobs because each phase can take several hours on a hosted runner.
"""

import os
import sys
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


def build():
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


def replay():
    run("env", "leanchecker", "-v", "BlackHole")


if __name__ == "__main__":
    phases = set(sys.argv[1:]) or {"--build", "--replay"}
    unknown = phases - {"--build", "--replay"}
    if unknown:
        sys.exit(f"unknown option(s): {' '.join(sorted(unknown))}")
    if "--build" in phases:
        build()
    if "--replay" in phases:
        replay()
