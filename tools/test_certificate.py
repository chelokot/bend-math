import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import certificate


class CertificateSearch(unittest.TestCase):
    def test_unit_circle_bounds_cosine(self):
        found = certificate.search(["cosine", "sine"], ["cosine"], ["cosine^2 + sine^2 - 1"], "1 - cosine",
                                   ["sine", "1 - cosine"], 2)
        self.assertIsNotNone(found)

    def test_tangent_line_of_unit_circle(self):
        found = certificate.search(["cosine", "sine"], [], ["cosine^2 + sine^2 - 1"], "5 - 4*cosine - 3*sine",
                                   ["5*cosine - 4", "5*sine - 3"], 2)
        self.assertIsNotNone(found)

    def test_defined_variable_is_reduced_away(self):
        found = certificate.search(["half"], [], ["half + half - 1"], "half", [], 1)
        self.assertEqual(found[0], 1)

    def test_false_goal_has_no_certificate(self):
        self.assertIsNone(certificate.search(["x"], ["x"], [], "1 - x", [], 2))


if __name__ == "__main__":
    unittest.main()
