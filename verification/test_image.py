import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import check_image
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

    def test_native_reference_rejects_sparse_substituted_and_truncated_images(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(check_image, "OUT", Path(directory)):
            path = Path(directory) / "zig-reference.f64"
            meta = {"shape": [160, 160, 4], "stride": 1, "eps": 0.01,
                    "snapshot_sha256": "c2d1dfdc8c92320ec77d22953f55c2b5d71b685496f5199c73a1280f20a0d537"}
            values = np.zeros((25600, 4), dtype="<f8")
            values.tofile(path)
            sidecar = path.with_name(path.name + ".json")
            sidecar.write_text(json.dumps(meta))
            self.assertEqual(check_image.read_reference(path.name).shape, (25600, 4))
            for key, replacement in [("stride", 40), ("snapshot_sha256", "substituted"), ("eps", 0.0025)]:
                sidecar.write_text(json.dumps(dict(meta, **{key: replacement})))
                with self.assertRaises(ValueError): check_image.read_reference(path.name)
            sidecar.write_text(json.dumps(meta))
            values[:1].tofile(path)
            with self.assertRaises(ValueError): check_image.read_reference(path.name)
            values[0, 0] = np.nan
            values.tofile(path)
            with self.assertRaises(ValueError): check_image.read_reference(path.name)


if __name__ == "__main__": unittest.main()
