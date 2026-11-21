import unittest

import numpy as np

import holographic


class ClosureAwareProjectionTests(unittest.TestCase):
    def test_record_keeps_exact_closure_and_unormalized_algebra(self):
        closed = holographic.closure_aware_projection("^v<>")
        self.assertTrue(closed.closure)
        self.assertEqual(closed.action, (0, 0, 0, 0))
        self.assertEqual(closed.pauli_fold, (1 + 0j, 0j, 0j, 1 + 0j))
        np.testing.assert_allclose(closed.xyz, [0, 0, 1], atol=1e-12)
        with self.assertRaises(ValueError):
            closed.xyz[0] = 9.0
        with self.assertRaises(ValueError):
            closed.spinor[0] = 9.0

    def test_closure_verdict_distinguishes_same_action_projection(self):
        open_history = holographic.closure_aware_projection("^v")
        closed_history = holographic.closure_aware_projection("^v<>")
        self.assertFalse(open_history.closure)
        self.assertTrue(closed_history.closure)
        self.assertEqual(open_history.action, closed_history.action)
        np.testing.assert_allclose(open_history.xyz, closed_history.xyz, atol=1e-12)
        self.assertNotEqual(open_history.pauli_fold, closed_history.pauli_fold)

    def test_record_is_explicitly_lossy_not_history_injective(self):
        a = holographic.closure_aware_projection("^v<>")
        b = holographic.closure_aware_projection("v^<>")
        self.assertEqual(a.action, b.action)
        self.assertEqual(a.closure, b.closure)
        # The original history remains an audit reference, not a recovered value.
        self.assertNotEqual(a.history, b.history)

    def test_invalid_history_is_refused(self):
        with self.assertRaises(ValueError):
            holographic.closure_aware_projection("^x")



if __name__ == "__main__":
    unittest.main()
