"""Unit tests for Mostowski Collapsing Theorem and Ordinal Rank.

Tests covering:
- Well-founded relations and minimal element detection
- Extensionality checks
- Transitive closure computation
- Inductive ordinal rank function
- Mostowski collapsing isomorphism
- Transitive sets and von Neumann ordinals
- WellFoundedStructure wrapper
- Verification that Coq formalization section_mostowski.v contains 0 Admitted
"""

import os
import subprocess
import unittest

from jech.mostowski import (
    WellFoundedStructure,
    find_minimal_element,
    is_extensional,
    is_minimal,
    is_transitive_set,
    is_well_founded,
    mostowski_collapse,
    predecessors,
    rank,
    transitive_closure,
    transitive_closure_relation,
    verify_mostowski_isomorphism,
    von_neumann_ordinal,
)


class TestWellFoundedness(unittest.TestCase):
    """Tests for well-founded relations and minimal elements."""

    def test_empty_relation(self):
        domain = []
        rel = []
        self.assertTrue(is_well_founded(domain, rel))

    def test_discrete_relation(self):
        domain = [1, 2, 3]
        rel = []
        self.assertTrue(is_well_founded(domain, rel))
        self.assertTrue(is_minimal(1, domain, rel))

    def test_linear_order_well_founded(self):
        # 0 E 1 E 2 E 3
        domain = [0, 1, 2, 3]
        rel = [(0, 1), (1, 2), (2, 3)]
        self.assertTrue(is_well_founded(domain, rel))
        self.assertEqual(find_minimal_element(domain, rel), 0)

    def test_subset_minimal_element(self):
        domain = [0, 1, 2, 3]
        rel = [(0, 1), (1, 2), (2, 3)]
        subset = [2, 3]
        self.assertEqual(find_minimal_element(subset, rel), 2)
        self.assertTrue(is_minimal(2, subset, rel))
        self.assertFalse(is_minimal(3, subset, rel))

    def test_cycle_not_well_founded(self):
        # 0 E 1 E 0
        domain = [0, 1]
        rel = [(0, 1), (1, 0)]
        self.assertFalse(is_well_founded(domain, rel))
        self.assertIsNone(find_minimal_element(domain, rel))

    def test_self_loop_not_well_founded(self):
        domain = [0, 1]
        rel = [(0, 0)]
        self.assertFalse(is_well_founded(domain, rel))


class TestExtensionality(unittest.TestCase):
    """Tests for extensional relations."""

    def test_extensional_linear_order(self):
        domain = [0, 1, 2]
        rel = [(0, 1), (0, 2), (1, 2)]
        self.assertTrue(is_extensional(domain, rel))

    def test_non_extensional_structure(self):
        # Two distinct elements with no predecessors
        domain = [0, 1]
        rel = []
        self.assertFalse(is_extensional(domain, rel))

    def test_non_extensional_shared_predecessors(self):
        # a E b and a E c with no other edges; pred(b) == pred(c) == {a}
        domain = ['a', 'b', 'c']
        rel = [('a', 'b'), ('a', 'c')]
        self.assertFalse(is_extensional(domain, rel))


class TestTransitiveClosure(unittest.TestCase):
    """Tests for transitive closure of relations and elements."""

    def test_predecessors(self):
        domain = [0, 1, 2, 3]
        rel = [(0, 2), (1, 2)]
        self.assertEqual(predecessors(2, domain, rel), {0, 1})
        self.assertEqual(predecessors(0, domain, rel), set())

    def test_transitive_closure_relation(self):
        domain = [0, 1, 2, 3]
        rel = [(0, 1), (1, 2), (2, 3)]
        tc = transitive_closure_relation(domain, rel)
        expected = {
            (0, 1), (1, 2), (2, 3),
            (0, 2), (1, 3), (0, 3)
        }
        self.assertEqual(tc, expected)

    def test_element_transitive_closure(self):
        domain = [0, 1, 2, 3]
        rel = [(0, 1), (1, 2), (2, 3)]
        self.assertEqual(transitive_closure(3, domain, rel), {0, 1, 2})
        self.assertEqual(transitive_closure(0, domain, rel), set())


class TestOrdinalRank(unittest.TestCase):
    """Tests for ordinal rank function."""

    def test_linear_order_ranks(self):
        domain = [0, 1, 2, 3]
        rel = [(0, 1), (1, 2), (2, 3)]
        ranks = rank(domain, rel)
        self.assertEqual(ranks, {0: 0, 1: 1, 2: 2, 3: 3})

    def test_diamond_ranks(self):
        # a E b, a E c, b E d, c E d
        domain = ['a', 'b', 'c', 'd']
        rel = [('a', 'b'), ('a', 'c'), ('b', 'd'), ('c', 'd')]
        ranks = rank(domain, rel)
        self.assertEqual(ranks['a'], 0)
        self.assertEqual(ranks['b'], 1)
        self.assertEqual(ranks['c'], 1)
        self.assertEqual(ranks['d'], 2)

    def test_rank_raises_on_cycle(self):
        domain = [0, 1]
        rel = [(0, 1), (1, 0)]
        with self.assertRaises(ValueError):
            rank(domain, rel)


class TestMostowskiCollapse(unittest.TestCase):
    """Tests for Mostowski collapsing isomorphism."""

    def test_collapse_von_neumann_ordinals(self):
        # Full membership structure on 3 elements:
        # 0 E 1, 0 E 2, 1 E 2
        domain = ['x0', 'x1', 'x2']
        rel = [('x0', 'x1'), ('x0', 'x2'), ('x1', 'x2')]
        cmap, m_set = mostowski_collapse(domain, rel)

        e0 = frozenset()
        e1 = frozenset([e0])
        e2 = frozenset([e0, e1])

        self.assertEqual(cmap['x0'], e0)
        self.assertEqual(cmap['x1'], e1)
        self.assertEqual(cmap['x2'], e2)
        self.assertEqual(m_set, frozenset([e0, e1, e2]))
        self.assertTrue(is_transitive_set(m_set))
        self.assertTrue(verify_mostowski_isomorphism(domain, rel, cmap))

    def test_collapse_tree_structure(self):
        # A well-founded extensional tree
        # 0 has no predecessors: pi(0) = {}
        # 1 has pred {0}: pi(1) = { { } }
        # 2 has pred {0, 1}: pi(2) = { {}, { {} } }
        domain = [0, 1, 2]
        rel = [(0, 1), (0, 2), (1, 2)]
        struct = WellFoundedStructure(domain, rel)
        self.assertTrue(struct.is_well_founded())
        self.assertTrue(struct.is_extensional())
        self.assertTrue(struct.verify_collapse())

    def test_collapse_raises_on_non_extensional(self):
        domain = [1, 2]
        rel = []
        with self.assertRaises(ValueError):
            mostowski_collapse(domain, rel)

    def test_collapse_raises_on_cycle(self):
        domain = [1, 2]
        rel = [(1, 2), (2, 1)]
        with self.assertRaises(ValueError):
            mostowski_collapse(domain, rel)


class TestVonNeumannOrdinals(unittest.TestCase):
    """Tests for von Neumann ordinal representations."""

    def test_ordinals(self):
        w0 = von_neumann_ordinal(0)
        w1 = von_neumann_ordinal(1)
        w2 = von_neumann_ordinal(2)
        w3 = von_neumann_ordinal(3)

        self.assertEqual(w0, frozenset())
        self.assertEqual(w1, frozenset([w0]))
        self.assertEqual(w2, frozenset([w0, w1]))
        self.assertEqual(w3, frozenset([w0, w1, w2]))

        self.assertTrue(is_transitive_set(w0))
        self.assertTrue(is_transitive_set(w1))
        self.assertTrue(is_transitive_set(w2))
        self.assertTrue(is_transitive_set(w3))

    def test_negative_ordinal_raises(self):
        with self.assertRaises(ValueError):
            von_neumann_ordinal(-1)


class TestCoqFormalization(unittest.TestCase):
    """Verify that section_mostowski.v compiles and contains 0 Admitted."""

    def test_coq_section_mostowski_proof_integrity(self):
        repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        v_file = os.path.join(repo_root, "section_mostowski.v")
        self.assertTrue(os.path.isfile(v_file), f"File {v_file} does not exist.")

        with open(v_file, "r") as f:
            content = f.read()

        self.assertNotIn("Admitted", content, "section_mostowski.v must not contain Admitted.")
        self.assertNotIn("admit.", content, "section_mostowski.v must not contain admit.")

        # Test Coq compilation
        res = subprocess.run(
            ["coqc", "-Q", ".", "", "section_mostowski.v"],
            cwd=repo_root,
            capture_output=True,
            text=True
        )
        self.assertEqual(res.returncode, 0, f"Coq compilation failed:\n{res.stderr}\n{res.stdout}")


if __name__ == "__main__":
    unittest.main()
