"""Binary32 check of the Faraday-cell integrals in geodesic.wesl (T2/T3/F2).

Every operation is rounded to binary32 exactly once, which is the most
accurate behaviour the WGSL accuracy table permits, and results are compared
with `mpmath` quadrature of the exact integrals
`ic = int_0^ds exp(-a s) cos(w s) ds`, `is = int_0^ds exp(-a s) sin(w s) ds`.

* `former`: the closed form used before (cancels for small optical depth);
* `current`: `ds * phi((a - i w) ds)` from `transfer_phi`.

The former form misses `is` by a factor of 260 at a = 1e-6, w = 1e-5, ds = 1;
the current form stays within 2.6e-7 ds over the grid below. Requires numpy and
mpmath.
"""

import itertools
import sys

import mpmath as mp
import numpy as np

mp.mp.dps = 50
f = np.float32


def rexp(x):
    return f(np.exp(np.float64(x)))


def rcos(x):
    return f(np.cos(np.float64(x)))


def rsin(x):
    return f(np.sin(np.float64(x)))


def former(alpha, w, ds):
    alpha, w, ds = f(alpha), f(w), f(ds)
    e = rexp(-(alpha * ds))
    angle = f(w * ds)
    den = f(f(alpha * alpha) + f(w * w))
    one_minus = f(f(1) - f(e * rcos(angle)))
    ic = f(f(f(alpha * one_minus) + f(f(w * e) * rsin(angle))) / den)
    is_ = f(f(f(w * one_minus) - f(f(alpha * e) * rsin(angle))) / den)
    return float(ic), float(is_)


COEFFICIENTS = [f(1 / mp.factorial(k + 1)) for k in range(11)]


def transfer_phi(zx, zy):
    zx, zy = f(zx), f(zy)
    if f(f(zx * zx) + f(zy * zy)) < f(0.25):
        ax, ay = COEFFICIENTS[10], f(0)
        for k in range(9, -1, -1):
            ax, ay = (f(COEFFICIENTS[k] - f(f(zx * ax) - f(zy * ay))),
                      f(-f(f(zx * ay) + f(zy * ax))))
        return ax, ay
    e = rexp(-zx)
    nx = f(f(1) - f(e * rcos(zy)))
    ny = f(e * rsin(zy))
    d = f(f(zx * zx) + f(zy * zy))
    return f(f(f(nx * zx) + f(ny * zy)) / d), f(f(f(ny * zx) - f(nx * zy)) / d)


def current(alpha, w, ds):
    alpha, w, ds = f(alpha), f(w), f(ds)
    rx, ry = transfer_phi(f(alpha * ds), -f(w * ds))
    return float(f(ds * rx)), float(f(ds * ry))


def exact(alpha, w, ds):
    a, w, ds = (mp.mpf(float(f(v))) for v in (alpha, w, ds))
    ic = mp.quad(lambda t: mp.e ** (-a * t) * mp.cos(w * t), [0, ds])
    is_ = mp.quad(lambda t: mp.e ** (-a * t) * mp.sin(w * t), [0, ds])
    return float(ic), float(is_)


def main():
    old = former(1e-6, 1e-5, 1.0)
    new = current(1e-6, 1e-5, 1.0)
    ref = exact(1e-6, 1e-5, 1.0)
    print(f"a=1e-6, w=1e-5, ds=1: exact is {ref[1]:.6e}, former {old[1]:.6e}, current {new[1]:.6e}")
    assert abs(old[1] - ref[1]) > 100 * abs(ref[1])
    worst = 0.0
    alphas = [1e-7, 1e-6, 1e-4, 1e-3, 0.01, 0.1, 0.3, 0.49, 0.51, 1.0, 3.0]
    ws = [1e-5, 1e-3, 0.1, 0.3, 0.35, 0.36, 0.5, 1.0, 5.0]
    for alpha, w, ds in itertools.product(alphas, ws, [1.0, 0.1]):
        if w * ds < 1e-5:
            continue
        got, want = current(alpha, w, ds), exact(alpha, w, ds)
        worst = max(worst, max(abs(got[0] - want[0]), abs(got[1] - want[1])) / ds)
    print(f"current kernel: worst |error| / ds = {worst:.2e}")
    assert worst < 2.6e-7
    return 0


if __name__ == "__main__":
    sys.exit(main())
