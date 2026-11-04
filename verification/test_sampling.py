"""Small regressions for coordinate and boundary conventions (no HDF5 required)."""

import unittest

import numpy as np
from eht_snapshot import (
    ME,
    MP,
    Snapshot,
    electron_temperature,
    ghost_cells,
    jacobian,
    to_native,
    to_world,
)


class SamplingTests(unittest.TestCase):
    def test_cartesian_roundtrip_and_vector_jacobian(self):
        rng = np.random.default_rng(9375)
        x = rng.uniform([0.3, 0.001, 0], [6, 0.999, 2 * np.pi], (100, 3))
        for spin in (-0.9375, 0, 0.9375):
            world = to_world(x, spin, 0.3)
            np.testing.assert_allclose(to_native(world, spin, 0.3), x, rtol=1e-10, atol=1e-11)
            j = jacobian(x, spin, 0.3)
            for axis in range(3):
                shift = np.eye(3)[axis] * 1e-5
                numerical = (to_world(x + shift, spin, 0.3) - to_world(x - shift, spin, 0.3)) / 2e-5
                np.testing.assert_allclose(j[:, 1:, axis + 1], numerical, rtol=3e-8, atol=1e-8)
        for world in ([0, 0, 0], [0, 2, 0], [float("nan"), 1, 2], [0.5, 0, 0]):
            with self.assertRaises(ValueError):
                to_native(world, 0.9375, 0.3)

    def test_reference_zero_field_temperature_floor(self):
        rho, energy = np.ones(3), np.array([1., 1., 1e-9])
        actual = electron_temperature(rho, energy, np.array([0., 1., 1.]), 1.444444)
        np.testing.assert_allclose(actual, [1e-3, (MP / ME) * 2 / 15, 1e-3], rtol=1e-14)

    def test_ghosts_rotate_poles_extend_radius_and_wrap_azimuth(self):
        data = np.arange(2 * 3 * 4 * 2).reshape(2, 3, 4, 2)
        ghosts = ghost_cells(data)
        np.testing.assert_array_equal(ghosts[0, 1:-1, 1:-1], data[0])
        np.testing.assert_array_equal(ghosts[-1, 1:-1, 1:-1], data[-1])
        np.testing.assert_array_equal(ghosts[1:-1, 0, 1:-1], np.roll(data[:, 0], 2, axis=1))
        np.testing.assert_array_equal(ghosts[1:-1, -1, 1:-1], np.roll(data[:, -1], 2, axis=1))
        np.testing.assert_array_equal(ghosts[:, :, 0], ghosts[:, :, -2])
        np.testing.assert_array_equal(ghosts[:, :, -1], ghosts[:, :, 1])
        with self.assertRaises(ValueError):
            ghost_cells(np.zeros((2, 3, 3, 1)))

    def test_cell_center_trilinear_interpolation_and_seam_continuity(self):
        snapshot = Snapshot.__new__(Snapshot)
        snapshot.start, snapshot.dx, snapshot.grid = np.zeros(3), np.ones(3), np.array([4, 4, 4])
        snapshot.stop = snapshot.grid.astype(float)
        i, j, k = np.meshgrid(*[np.arange(4) + 0.5] * 3, indexing="ij")
        polynomial = lambda x, y, z: 2 + 3*x - y + x*y + z + x*y*z
        values = ghost_cells(polynomial(i, j, k)[..., None])
        points = np.array([[0.6, 1.3, 2.9], [1.2, 2.3, 1.9], [2.5, 2.5, 2.5]])
        np.testing.assert_allclose(snapshot.interpolate(values, points)[:, 0], polynomial(*points.T))
        seam = snapshot.interpolate(values, np.array([[1.2, 1.3, 0], [1.2, 1.3, 4], [1.2, 1.3, -4]]))
        np.testing.assert_array_equal(seam, np.repeat(seam[:1], 3, axis=0))
        # The radial ghost copies the edge, rather than extrapolating the polynomial.
        a = snapshot.interpolate(values, np.array([[0, 1.3, 2.9], [0.5, 1.3, 2.9]]))
        np.testing.assert_array_equal(a[0], a[1])


if __name__ == "__main__":
    unittest.main()
