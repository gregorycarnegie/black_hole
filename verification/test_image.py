import unittest

import numpy as np

from outer_ray import geometry


class OuterGeometryTests(unittest.TestCase):
    def test_inverse_and_cartesian_metric_derivatives(self):
        x=np.array([[120.,-17.,5.],[23.,150.,-80.],[3000.,-9500.,7.]])
        _,g,inv,dg=geometry(x)
        np.testing.assert_allclose(g@inv,np.broadcast_to(np.eye(4),g.shape),atol=1e-15,rtol=0)
        for axis in range(3):
            shift=np.eye(3)[axis]*0.01
            numerical=(geometry(x+shift)[1]-geometry(x-shift)[1])/0.02
            np.testing.assert_allclose(dg[:,axis],numerical,atol=1e-12,rtol=2e-7)


if __name__ == "__main__": unittest.main()
