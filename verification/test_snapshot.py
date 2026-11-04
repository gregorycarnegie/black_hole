"""Reject a different snapshot or coordinate/primitive interpretation."""

import json
import unittest

from check_snapshot import MANIFEST, check_header


class SnapshotHeaderTests(unittest.TestCase):
    def test_rounded_paper_time_cannot_replace_actual_snapshot_time(self):
        header = json.loads(MANIFEST.read_text(encoding="utf-8"))["header"]
        with self.assertRaisesRegex(ValueError, "time"):
            check_header({**header, "time": 4500.0}, header)

    def test_wrong_coordinates_and_primitive_order_are_rejected(self):
        header = json.loads(MANIFEST.read_text(encoding="utf-8"))["header"]
        for key, value in (("metric", "Cartesian"), ("primitive_names", list(reversed(header["primitive_names"]))), ("grid", [128, 128, 128]), ("spin", 0.94)):
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, key):
                check_header({**header, key: value}, header)


if __name__ == "__main__":
    unittest.main()
