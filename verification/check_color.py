"""Check `blackbody_color` in geodesic.wesl against Planck colours (obligation V3).

The shader colours the thin disk with `blackbody_color(s)`, where
`s = nt_temp(r) / 0.488` is the temperature divided by its peak. A physical
blackbody colour would be the chromaticity of a Planck spectrum at
`T = s * T_peak` for some peak temperature. This script evaluates Planck
spectra with the CIE 1931 2-degree observer (1 nm table) and the linear sRGB
(Rec. 709, D65) primaries, then shows that no `T_peak` is consistent with the
shader's three colour stops.

The reference transform and error metric are fixed here:
  * spectrum: Planck's law, any temperature T > 0;
  * colour: linear sRGB from CIE XYZ, compared through the ratios G/R and B/R,
    which do not depend on the unspecified brightness normalisation.

Both ratios increase strictly with temperature on the grid used below
(checked), so each shader stop determines a unique temperature per ratio.
Requires `numpy` and `colour-science`.
"""

import sys
import warnings

import numpy as np

warnings.filterwarnings("ignore")
import colour  # noqa: E402

CMFS = colour.MSDS_CMFS["CIE 1931 2 Degree Standard Observer"]
WAVELENGTH = CMFS.wavelengths * 1e-9
XYZ_BAR = CMFS.values
XYZ_TO_SRGB = np.array([
    [3.2404542, -1.5371385, -0.4985314],
    [-0.9692660, 1.8760108, 0.0415560],
    [0.0556434, -0.2040259, 1.0572252],
])
H, C, K = 6.62607015e-34, 299792458.0, 1.380649e-23

# Shader colour stops: blackbody_color(0.4), (0.75), (1.0).
STOPS = [(0.4, (1.0, 0.35, 0.02)), (0.75, (1.0, 0.95, 0.80)), (1.0, (0.65, 0.80, 1.0))]


def linear_srgb(temperature):
    radiance = 1.0 / WAVELENGTH**5 / np.expm1(H * C / (WAVELENGTH * K * temperature))
    return XYZ_TO_SRGB @ (XYZ_BAR * radiance[:, None]).sum(axis=0)


def main():
    temperatures = np.geomspace(500.0, 1.0e5, 20000)
    colours = np.array([linear_srgb(t) for t in temperatures])
    green = colours[:, 1] / colours[:, 0]
    blue = colours[:, 2] / colours[:, 0]
    assert np.all(np.diff(green) > 0) and np.all(np.diff(blue[blue > 0]) > 0)

    def temperature(ratio, table):
        index = np.searchsorted(table, ratio)
        assert 0 < index < len(table), ratio
        return temperatures[index - 1], temperatures[index]

    from_blue = {}
    for s, (r, g, b) in STOPS:
        low, high = temperature(b / r, blue)
        from_blue[s] = (low, high)
        print(f"s={s}: B/R={b / r:.3f} -> T in [{low:.0f}, {high:.0f}] K", end="")
        if g / r < green[-1]:
            glow, ghigh = temperature(g / r, green)
            print(f"; G/R={g / r:.3f} -> T in [{glow:.0f}, {ghigh:.0f}] K")
            # A Planck colour has one temperature; disjoint intervals mean the
            # stop is not on the Planck locus at all.
            if s == 0.4:
                assert ghigh < low or glow > high
        else:
            print(f"; G/R={g / r:.3f} exceeds every Planck colour")

    # T = s * T_peak requires T(0.75)/T(0.4) = 1.875 and T(1)/T(0.75) = 4/3.
    ratio_low = from_blue[0.75][0] / from_blue[0.4][1]
    ratio_high = from_blue[1.0][0] / from_blue[0.75][1]
    print(f"T(0.75)/T(0.4) >= {ratio_low:.3f} (linear mapping needs 1.875)")
    print(f"T(1)/T(0.75)  >= {ratio_high:.3f} (linear mapping needs 1.333)")
    assert ratio_low > 1.875 * 1.3 and ratio_high > 4 / 3 * 1.15
    print("No peak temperature makes blackbody_color a Planck colour sequence.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
