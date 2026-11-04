"""The pinned fast-light MKS snapshot in the renderer's Cartesian (+Y spin) frame.

Conventions match ipole's iharm model at the commit in eht-reference.json.
This module supplies benchmark data, not the application's prescribed plasma.
"""

import json
from pathlib import Path

import h5py
import numpy as np
from check_snapshot import MANIFEST, check_snapshot

CL, MP, ME = 2.99792458e10, 1.67262171e-24, 9.1093826e-28
L_UNIT = 6.6742e-8 * 6.2e9 * 1.989e33 / CL**2
RHO_UNIT = 1.672e26 / L_UNIT**3
B_UNIT = CL * np.sqrt(4 * np.pi * RHO_UNIT)


def theta(x2, hslope):
    return np.pi * x2 + 0.5 * (1 - hslope) * np.sin(2 * np.pi * x2)


def to_world(x, spin, hslope):
    r, th, phi = np.exp(x[..., 0]), theta(x[..., 1], hslope), x[..., 2]
    s, c = np.sin(th), np.cos(th)
    cp, sp = np.cos(phi), np.sin(phi)
    return np.stack(((r * cp - spin * sp) * s, r * c, -(r * sp + spin * cp) * s), axis=-1)


def to_native(pos, spin, hslope):
    pos = np.asarray(pos, dtype=np.float64)
    if not np.isfinite(pos).all():
        raise ValueError("Nonfinite Cartesian position")
    if np.any((pos[..., 0] == 0) & (pos[..., 2] == 0)):
        raise ValueError("Azimuth is undefined on the polar axis")
    q = np.sum(pos**2, axis=-1) - spin**2
    root = np.sqrt(q**2 + 4 * (spin * pos[..., 1])**2)
    r2 = 0.5 * (q + root)
    # Rationalization avoids cancellation near the equatorial disk.
    r2 = np.where(q < 0, 2 * (spin * pos[..., 1])**2 / np.maximum(root - q, 1e-300), r2)
    if np.any(r2 <= 0):
        raise ValueError("Position on the singular Kerr coordinate disk")
    r = np.sqrt(r2)
    th = np.arccos(np.clip(pos[..., 1] / r, -1, 1))
    lo, hi = np.zeros_like(r), np.ones_like(r)
    for _ in range(56):
        mid = (lo + hi) * 0.5
        below = theta(mid, hslope) < th
        lo, hi = np.where(below, mid, lo), np.where(below, hi, mid)
    phi = np.arctan2(-r * pos[..., 2] - spin * pos[..., 0], r * pos[..., 0] - spin * pos[..., 2])
    return np.stack((np.log(r), (lo + hi) * 0.5, phi % (2 * np.pi)), axis=-1)


def jacobian(x, spin, hslope):
    """d(t,world_x,world_y,world_z) / d(t,x1,x2,x3)."""
    x = np.asarray(x)
    r, th, phi = np.exp(x[..., 0]), theta(x[..., 1], hslope), x[..., 2]
    s, c, cp, sp = np.sin(th), np.cos(th), np.cos(phi), np.sin(phi)
    dth = np.pi * (1 + (1 - hslope) * np.cos(2 * np.pi * x[..., 1]))
    j = np.zeros(x.shape[:-1] + (4, 4))
    j[..., 0, 0] = 1
    j[..., 1:, 1] = np.stack((r * cp * s, r * c, -r * sp * s), axis=-1)
    j[..., 1:, 2] = np.stack(((r * cp - spin * sp) * c, -r * s, -(r * sp + spin * cp) * c), axis=-1) * dth[..., None]
    j[..., 1:, 3] = np.stack((-(r * sp + spin * cp) * s, np.zeros_like(r), -(r * cp - spin * sp) * s), axis=-1)
    return j


def native_metric(x, spin, hslope):
    r, th = np.exp(x[..., 0]), theta(x[..., 1], hslope)
    s2, rho2 = np.sin(th)**2, r**2 + (spin * np.cos(th))**2
    f = 2 * r / rho2
    g = np.zeros(x.shape[:-1] + (4, 4))
    g[..., 0, 0], g[..., 0, 1], g[..., 0, 3] = -1 + f, f, -spin * f * s2
    g[..., 1, 1], g[..., 1, 3] = 1 + f, -spin * s2 * (1 + f)
    g[..., 2, 2], g[..., 3, 3] = rho2, s2 * (rho2 + spin**2 * s2 * (1 + f))
    g += np.swapaxes(np.triu(g, 1), -1, -2)
    d = np.stack((np.ones_like(r), r, np.pi * (1 + (1 - hslope) * np.cos(2 * np.pi * x[..., 1])), np.ones_like(r)), axis=-1)
    return g * d[..., :, None] * d[..., None, :]


def four_vectors(p, g):
    inv = np.linalg.inv(g)
    v2 = np.einsum("...i,...ij,...j->...", p[..., 2:5], g[..., 1:, 1:], p[..., 2:5])
    fac = np.sqrt(-(1 + np.abs(v2)) / inv[..., 0, 0])
    u = np.concatenate(((-fac * inv[..., 0, 0])[..., None], p[..., 2:5] - fac[..., None] * inv[..., 0, 1:]), axis=-1)
    ucov = np.einsum("...ij,...j->...i", g, u)
    b0 = np.sum(p[..., 5:8] * ucov[..., 1:], axis=-1)
    b = np.concatenate((b0[..., None], (p[..., 5:8] + u[..., 1:] * b0[..., None]) / u[..., :1]), axis=-1)
    return u, b


def electron_temperature(rho, energy, bsq, gamma):
    # Preserve the reference's zero-field NaN-to-floor behavior, even at fixed Tp/Te.
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        beta2 = (2 * energy * (gamma - 1) / bsq)**2
        trat = 3 * beta2 / (1 + beta2) + 3 / (1 + beta2)
        game, gamp = 1.333333333333333, 1.666666666666667
        scale = (MP / ME) * (game - 1) * (gamp - 1) / ((gamp - 1) + (game - 1) * trat)
        return np.fmax(scale * energy / rho, 1e-3)


def ghost_cells(values):
    n1, n2, n3 = values.shape[:3]
    if n3 % 2:
        raise ValueError("Pinned MKS snapshot requires an even azimuthal grid")
    out = np.empty((n1 + 2, n2 + 2, n3 + 2) + values.shape[3:], dtype=values.dtype)
    out[1:-1, 1:-1, 1:-1] = values
    out[0, 1:-1, 1:-1], out[-1, 1:-1, 1:-1] = values[0], values[-1]
    out[:, 0, 1:-1] = np.roll(out[:, 1, 1:-1], n3 // 2, axis=1)
    out[:, -1, 1:-1] = np.roll(out[:, -2, 1:-1], n3 // 2, axis=1)
    out[:, :, 0], out[:, :, -1] = out[:, :, -2], out[:, :, 1]
    return out


class Snapshot:
    def __init__(self, path):
        self.identity = check_snapshot(Path(path))
        with h5py.File(path, "r") as source:
            self.spin = float(source["header/geom/mks/a"][()])
            self.hslope = float(source["header/geom/mks/hslope"][()])
            gamma = float(source["header/gam"][()])
            self.start = np.array([source[f"header/geom/startx{i}"][()] for i in (1, 2, 3)])
            self.dx = np.array([source[f"header/geom/dx{i}"][()] for i in (1, 2, 3)])
            p = source["prims"][...].astype(np.float64)
        self.grid = np.array(p.shape[:3])
        self.stop = self.start + self.grid * self.dx
        self.primitives = ghost_cells(p)
        physical = np.empty(p.shape[:3] + (4,))
        for i in range(self.grid[0]):
            x = self.start + self.dx * np.stack(np.meshgrid([i + 0.5], np.arange(self.grid[1]) + 0.5, np.arange(self.grid[2]) + 0.5, indexing="ij"), axis=-1)
            g = native_metric(x[0], self.spin, self.hslope)
            _, b = four_vectors(p[i], g)
            bsq = np.einsum("...i,...ij,...j->...", b, g, b)
            if np.any(bsq < 0):
                raise ValueError("Negative cell magnetic norm")
            physical[i, ..., 0] = p[i, ..., 0] * RHO_UNIT / (MP + ME)
            physical[i, ..., 1] = electron_temperature(p[i, ..., 0], p[i, ..., 1], bsq, gamma)
            physical[i, ..., 2] = np.sqrt(bsq) * B_UNIT
            physical[i, ..., 3] = np.maximum(bsq / p[i, ..., 0], 1e-40)
        self.physical = ghost_cells(physical)

    def interpolate(self, values, x):
        x = np.array(x, dtype=np.float64, copy=True)
        x[..., 2] %= self.stop[2]
        base = np.clip(np.floor((x - self.start) / self.dx - 0.5).astype(int), -1, self.grid - 1)
        d = np.clip((x - (self.start + (base + 0.5) * self.dx)) / self.dx, 0, 1)
        base += 1
        result = np.zeros(x.shape[:-1] + values.shape[3:])
        for k in (0, 1):
            for j in (0, 1):
                for i in (0, 1):
                    w = (d[..., 0] if i else 1 - d[..., 0]) * (d[..., 1] if j else 1 - d[..., 1]) * (d[..., 2] if k else 1 - d[..., 2])
                    result += values[base[..., 0] + i, base[..., 1] + j, base[..., 2] + k] * w[..., None]
        return result

    def sample(self, x):
        x = np.asarray(x, dtype=np.float64)
        if not np.isfinite(x).all() or np.any(x[..., :2] < self.start[:2]) or np.any(x[..., :2] >= self.stop[:2]) or np.any(x[..., 1] == 0):
            raise ValueError("Query outside the finite MKS grid")
        p, physical = self.interpolate(self.primitives, x), self.interpolate(self.physical, x)
        u, b = four_vectors(p, native_metric(x, self.spin, self.hslope))
        physical[..., 0] = np.where(physical[..., 3] < 1, physical[..., 0], 0)
        return p, u, b, physical


def default_path():
    return Path(__file__).resolve().parent.parent / "target/eht-benchmark" / json.loads(MANIFEST.read_text(encoding="utf-8"))["filename"]
