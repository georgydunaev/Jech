"""Unit tests for Cumulative Hierarchy V_alpha, Foundation, and Reflection."""

import os
import subprocess
import unittest

from jech.cumulative_hierarchy import (
    EMPTY_SET,
    AtomEq,
    AtomIn,
    FAll,
    FAnd,
    FBoundedAll,
    FBoundedEx,
    FEx,
    FImp,
    FNot,
    FOr,
    evaluate_formula,
    find_in_minimal_element,
    find_reflection_stages,
    generate_stages,
    is_delta_0,
    is_transitive_stage,
    is_well_founded_set,
    is_witness_closed,
    least_stage_containing,
    powerset,
    set_rank,
    transitive_closure_set,
    v_stage,
    verify_delta_0_reflection,
    verify_foundation_on_stage,
    verify_monotonicity,
    von_neumann_ordinal_set,
)


class TestCumulativeStages(unittest.TestCase):
    """Test computation and structural properties of cumulative hierarchy stages V_n."""

    def test_stage_cardinalities(self):
        """Test |V_0| = 0, |V_1| = 1, |V_2| = 2, |V_3| = 4, |V_4| = 16."""
        stages = generate_stages(4)
        expected_sizes = {0: 0, 1: 1, 2: 2, 3: 4, 4: 16}
        for n, size in expected_sizes.items():
            self.assertEqual(len(stages[n]), size, f"Failed cardinality check for V_{n}")

    def test_v_0_is_empty(self):
        """Test V_0 is the empty set."""
        v0 = v_stage(0)
        self.assertEqual(len(v0), 0)
        self.assertEqual(v0, frozenset())

    def test_v_1_contains_only_empty(self):
        """Test V_1 = { empty }."""
        v1 = v_stage(1)
        self.assertEqual(v1, frozenset([EMPTY_SET]))

    def test_stage_transitivity(self):
        """Test transitivity of each stage V_0 through V_4."""
        stages = generate_stages(4)
        for n in range(5):
            self.assertTrue(
                is_transitive_stage(stages[n]),
                f"Stage V_{n} should be transitive"
            )

    def test_stage_monotonicity(self):
        """Test cumulative monotonicity: i <= j implies V_i subset V_j."""
        stages = generate_stages(4)
        self.assertTrue(verify_monotonicity(stages))

    def test_successor_power_set_property(self):
        """Test x in V_{n+1} iff x subset V_n."""
        stages = generate_stages(3)
        for n in range(3):
            vn = stages[n]
            vn1 = stages[n + 1]
            for x in vn1:
                self.assertTrue(x.issubset(vn))


class TestSetRank(unittest.TestCase):
    """Test ordinal rank computation for hereditarily finite sets."""

    def test_empty_set_rank(self):
        """Test rank(empty) = 0."""
        self.assertEqual(set_rank(EMPTY_SET), 0)

    def test_von_neumann_ordinal_ranks(self):
        """Test rank(n) = n for von Neumann ordinals."""
        for n in range(5):
            vn = von_neumann_ordinal_set(n)
            self.assertEqual(set_rank(vn), n)

    def test_least_stage_containing(self):
        """Test x in V_n iff rank(x) < n."""
        for n in range(4):
            vn = von_neumann_ordinal_set(n)
            least_n = least_stage_containing(vn, max_stage=4)
            self.assertEqual(least_n, n + 1)

    def test_rank_strictly_increasing_along_membership(self):
        """Test y in x implies rank(y) < rank(x)."""
        stages = generate_stages(3)
        for x in stages[3]:
            for y in x:
                self.assertLess(set_rank(y), set_rank(x))


class TestFoundationAndAcyclicity(unittest.TestCase):
    """Test Axiom of Regularity / Foundation, minimal elements, and acyclicity."""

    def test_well_founded_set_detection(self):
        """Test well-foundedness detection on hereditarily finite sets."""
        v3 = v_stage(3)
        for x in v3:
            self.assertTrue(is_well_founded_set(x))

    def test_find_in_minimal_element(self):
        """Test in-minimal element property: m in S and m intersection S is empty."""
        v3 = v_stage(3)
        for x in v3:
            if x:
                m = find_in_minimal_element(x)
                self.assertIsNotNone(m)
                self.assertIn(m, x)
                self.assertEqual(len(m & x), 0)

    def test_verify_foundation_on_stages(self):
        """Test regularity verification on all stages V_0 through V_4."""
        stages = generate_stages(4)
        for n in range(5):
            self.assertTrue(verify_foundation_on_stage(stages[n]))

    def test_transitive_closure(self):
        """Test TC(x) is transitive and x is subset of TC(x)."""
        v3 = v_stage(3)
        for x in v3:
            tc = transitive_closure_set(x)
            self.assertTrue(x.issubset(tc))
            self.assertTrue(is_transitive_stage(tc))


class TestSetFormulasAndDelta0Reflection(unittest.TestCase):
    """Test first-order formula semantics and Delta_0 absoluteness."""

    def setUp(self):
        self.stages = generate_stages(4)
        self.vn0 = von_neumann_ordinal_set(0)  # empty
        self.vn1 = von_neumann_ordinal_set(1)  # {0}
        self.vn2 = von_neumann_ordinal_set(2)  # {0, 1}

    def test_atomic_formulas(self):
        """Test atomic equality and membership evaluation."""
        env = {"x": self.vn0, "y": self.vn1, "z": self.vn0}
        v2 = self.stages[2]

        eq_true = AtomEq("x", "z")
        eq_false = AtomEq("x", "y")
        in_true = AtomIn("x", "y")
        in_false = AtomIn("y", "x")

        self.assertTrue(evaluate_formula(eq_true, env, v2))
        self.assertFalse(evaluate_formula(eq_false, env, v2))
        self.assertTrue(evaluate_formula(in_true, env, v2))
        self.assertFalse(evaluate_formula(in_false, env, v2))

    def test_boolean_connectives(self):
        """Test negation, conjunction, disjunction, and implication."""
        env = {"x": self.vn0, "y": self.vn1}
        v2 = self.stages[2]

        phi_true = AtomIn("x", "y")
        phi_false = AtomEq("x", "y")

        self.assertFalse(evaluate_formula(FNot(phi_true), env, v2))
        self.assertTrue(evaluate_formula(FNot(phi_false), env, v2))
        self.assertTrue(evaluate_formula(FAnd(phi_true, phi_true), env, v2))
        self.assertFalse(evaluate_formula(FAnd(phi_true, phi_false), env, v2))
        self.assertTrue(evaluate_formula(FOr(phi_true, phi_false), env, v2))
        self.assertTrue(evaluate_formula(FImp(phi_false, phi_true), env, v2))

    def test_delta_0_predicate(self):
        """Test identification of Delta_0 formulas."""
        f_delta0 = FBoundedAll("u", "y", FBoundedEx("v", "u", AtomIn("v", "z")))
        f_unbounded = FAll("u", AtomEq("u", "u"))

        self.assertTrue(is_delta_0(f_delta0))
        self.assertFalse(is_delta_0(f_unbounded))

    def test_delta_0_absoluteness_across_stages(self):
        """Test Delta_0 reflection between V_2, V_3, and V_4."""
        phi = FBoundedAll("x", "y", FOr(AtomIn("x", "z"), AtomEq("x", "w")))
        self.assertTrue(is_delta_0(phi))

        env = {"y": self.vn2, "z": self.vn1, "w": self.vn0}
        v2 = self.stages[2]
        v3 = self.stages[3]
        v4 = self.stages[4]

        self.assertTrue(verify_delta_0_reflection(phi, env, v2, v3))
        self.assertTrue(verify_delta_0_reflection(phi, env, v3, v4))
        self.assertTrue(verify_delta_0_reflection(phi, env, v2, v4))


class TestMontagueLevyReflection(unittest.TestCase):
    """Test Tarski-Vaught witness closure and reflection stage discovery."""

    def setUp(self):
        self.stages = generate_stages(4)
        self.vn0 = von_neumann_ordinal_set(0)
        self.vn1 = von_neumann_ordinal_set(1)

    def test_witness_closure_property(self):
        """Test Tarski-Vaught witness condition between V_2 and V_4."""
        # Witness condition for: exists u, u in y
        env = {"y": self.vn1}
        phi = AtomIn("u", "y")

        self.assertTrue(
            is_witness_closed(phi, "u", env, self.stages[2], self.stages[4])
        )

    def test_reflection_stage_discovery(self):
        """Test finding reflection stages for first-order formula."""
        env = {"y": self.vn1}
        # Formula: exists u in domain, u is empty and u in y
        phi = FEx("u", FAnd(AtomIn("u", "y"), FBoundedAll("v", "u", AtomEq("v", "v"))))

        refl_stages = find_reflection_stages(phi, env, self.stages, target_stage=4)
        self.assertIn(2, refl_stages)
        self.assertIn(3, refl_stages)
        self.assertIn(4, refl_stages)


class TestCoqCumulativeHierarchyIntegrity(unittest.TestCase):
    """Verify Coq formalization section_cumulative_hierarchy.v compiles with 0 Admitted."""

    def test_coq_compilation_and_zero_admitted(self):
        """Test coqc section_cumulative_hierarchy.v and verify zero Admitted/admit."""
        root_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        v_file = os.path.join(root_dir, "section_cumulative_hierarchy.v")
        self.assertTrue(os.path.isfile(v_file), "section_cumulative_hierarchy.v not found")

        # Check for admit or Admitted
        with open(v_file, "r") as f:
            content = f.read()

        self.assertNotIn("Admitted", content, "section_cumulative_hierarchy.v contains Admitted")
        self.assertNotIn("admit", content, "section_cumulative_hierarchy.v contains admit")

        # Check compilation with coqc
        cmd = ["coqc", "-Q", root_dir, "", v_file]
        res = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(
            res.returncode, 0,
            f"Coq compilation failed:\nstdout: {res.stdout}\nstderr: {res.stderr}"
        )


if __name__ == "__main__":
    unittest.main()
