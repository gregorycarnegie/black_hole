#!/usr/bin/env python3
"""Compile `tools/cuda/kernels.rs` with `cargo-oxide` and write `src/compute/kernels.ptx`."""

from __future__ import annotations

import hashlib
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OXIDE_DIR = ROOT / "tools" / "cuda" / "oxide"
OUT_PTX = ROOT / "src" / "compute" / "kernels.ptx"
SOURCE_FILES = [
    ROOT / "tools" / "cuda" / "kernels.rs",
    OXIDE_DIR / "Cargo.toml",
    OXIDE_DIR / "Cargo.lock",
    OXIDE_DIR / "rust-toolchain.toml",
    OXIDE_DIR / "src" / "main.rs",
]


def source_sha256() -> str:
    digest = hashlib.sha256()
    for path in SOURCE_FILES:
        rel = path.relative_to(ROOT).as_posix()
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes().replace(b"\r\n", b"\n"))
        digest.update(b"\0")
    return digest.hexdigest()


def to_wsl_path(path: Path) -> str:
    drive = path.drive.rstrip(":").lower()
    tail = path.as_posix().split(":", 1)[1]
    return f"/mnt/{drive}{tail}"


def main() -> int:
    if os.name == "nt":
        wsl_dir = to_wsl_path(OXIDE_DIR)
        cmd = [
            "wsl",
            "-e",
            "bash",
            "-lc",
            f'export PATH="$HOME/.cargo/bin:$PATH" && cd "{wsl_dir}" && cargo oxide build --arch sm_80',
        ]
    else:
        cmd = ["cargo", "oxide", "build", "--arch", "sm_80"]

    subprocess.run(cmd, cwd=OXIDE_DIR if os.name != "nt" else None, check=True)

    emitted = OXIDE_DIR / "black_hole_cuda_kernels.ptx"
    if not emitted.is_file():
        raise FileNotFoundError(f"Expected PTX output at {emitted}")

    ptx_body = emitted.read_text(encoding="utf-8").replace("\r\n", "\n")
    emitted.unlink()
    for ll in OXIDE_DIR.glob("*.ll"):
        ll.unlink(missing_ok=True)

    sha = source_sha256()
    OUT_PTX.write_text(f"// Source SHA256: {sha}\n{ptx_body}", encoding="utf-8", newline="\n")
    print(f"Wrote {OUT_PTX.relative_to(ROOT)} (SHA256: {sha})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
