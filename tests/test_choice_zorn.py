"""Unit tests for Axiom of Choice, Zorn's Lemma, Well-Ordering, and Tukey's Lemma."""

import unittest

from jech.choice_zorn import (
    cartesian_product_choice,
    choice_function,
    find_all_chains,
    find_least_element,
    find_maximal_chains,
    find_maximal_element_tukey,
    find_maximal_elements,
    has_choice_function,
    is_chain,
    is_chain_bounded,
    is_finite_character,
    is_linear_order,
    is_maximal_element,
    is_partial_order,
    is_well_ordering,
    upper_bounds,
    verify_tukey_lemma,
    verify_well_ordering_theorem,
    well_order_from_choice,
    zorn_find_maximal,
)


class TestChoiceFunctions(unittest.TestCase):
    """Test choice function extraction and Cartesian product choice."""

    def test_choice_function_basic(self):
        """Test choice function selection on disjoint non-empty sets."""
        family = [frozenset({1, 2}), frozenset({3, 4}), frozenset({5})]
        f = choice_function(family)
        for s in family:
            self.assertIn(s, f)
            self.assertIn(f[s], s)

    def test_choice_function_non_disjoint(self):
        """Test choice function on overlapping non-empty sets."""
        family = [frozenset({1, 2}), frozenset({2, 3}), frozenset({1, 3})]
        f = choice_function(family)
        for s in family:
            self.assertIn(s, f)
            self.assertIn(f[s], s)

    def test_choice_function_empty_family(self):
        """Test choice function on empty collection."""
        f = choice_function([])
        self.assertEqual(f, {})

    def test_choice_function_rejects_empty_set(self):
        """Test that choice function raises ValueError when family contains empty set."""
        family = [frozenset({1, 2}), frozenset()]
        with self.assertRaises(ValueError):
            choice_function(family)

    def test_has_choice_function(self):
        """Test verification predicate has_choice_function."""
        self.assertTrue(has_choice_function([frozenset({1}), frozenset({2, 3})]))
        self.assertTrue(has_choice_function([]))
        self.assertFalse(has_choice_function([frozenset({1}), frozenset()]))

    def test_choice_function_custom_chooser(self):
        """Test choice function with maximum element strategy."""
        family = [frozenset({1, 5, 3}), frozenset({10, 20})]
        f = choice_function(family, strategy=max)
        self.assertEqual(f[frozenset({1, 5, 3})], 5)
        self.assertEqual(f[frozenset({10, 20})], 20)

    def test_cartesian_product_choice(self):
        """Test choice of tuple in Cartesian product of non-empty sets."""
        s1 = frozenset({"a", "b"})
        s2 = frozenset({1, 2, 3})
        s3 = frozenset({True})
        tuple_choice = cartesian_product_choice(s1, s2, s3)
        self.assertEqual(len(tuple_choice), 3)
        self.assertIn(tuple_choice[0], s1)
        self.assertIn(tuple_choice[1], s2)
        self.assertIn(tuple_choice[2], s3)

    def test_cartesian_product_choice_empty_component(self):
        """Test that Cartesian product choice raises ValueError if any component is empty."""
        s1 = frozenset({"a"})
        s2 = frozenset()
        with self.assertRaises(ValueError):
            cartesian_product_choice(s1, s2)


class TestPosetsAndChains(unittest.TestCase):
    """Test partial orders, linear orders, chains, and upper bounds."""

    def setUp(self):
        """Set up standard subset poset on powerset of {1, 2}."""
        self.ground = [
            frozenset(),
            frozenset({1}),
            frozenset({2}),
            frozenset({1, 2}),
        ]
        self.subset_le = {
            (a, b) for a in self.ground for b in self.ground if a.issubset(b)
        }

    def test_is_partial_order_true(self):
        """Test that subset inclusion is a valid partial order."""
        self.assertTrue(is_partial_order(self.ground, self.subset_le))

    def test_is_linear_order_false_on_powerset(self):
        """Test that subset inclusion on powerset is not linear."""
        self.assertFalse(is_linear_order(self.ground, self.subset_le))

    def test_is_linear_order_true_on_chain(self):
        """Test linear order on integers with standard less-than-or-equal."""
        elements = [1, 2, 3, 4]
        le = {(a, b) for a in elements for b in elements if a <= b}
        self.assertTrue(is_partial_order(elements, le))
        self.assertTrue(is_linear_order(elements, le))

    def test_partial_order_failure_cases(self):
        """Test non-reflexive, non-antisymmetric, and non-transitive relations."""
        elements = [1, 2]
        # Not reflexive
        self.assertFalse(is_partial_order(elements, {(1, 1)}))
        # Not antisymmetric
        self.assertFalse(is_partial_order(elements, {(1, 1), (2, 2), (1, 2), (2, 1)}))
        # Not transitive
        self.assertFalse(
            is_partial_order([1, 2, 3], {(1, 1), (2, 2), (3, 3), (1, 2), (2, 3)})
        )

    def test_is_chain(self):
        """Test chain detection in subset poset."""
        chain_valid = [frozenset(), frozenset({1}), frozenset({1, 2})]
        chain_invalid = [frozenset({1}), frozenset({2})]
        self.assertTrue(is_chain(chain_valid, self.subset_le))
        self.assertFalse(is_chain(chain_invalid, self.subset_le))

    def test_upper_bounds(self):
        """Test computation of upper bounds for a chain."""
        chain = [frozenset(), frozenset({1})]
        bounds = upper_bounds(chain, self.ground, self.subset_le)
        self.assertEqual(bounds, {frozenset({1}), frozenset({1, 2})})

    def test_is_chain_bounded(self):
        """Test chain boundedness predicate for all chains in domain."""
        self.assertTrue(is_chain_bounded(self.ground, self.subset_le))

    def test_find_all_chains(self):
        """Test enumeration of all chains in a small poset."""
        chains = find_all_chains(self.ground, self.subset_le)
        # Empty chain is a chain
        self.assertIn(frozenset(), chains)
        # Singletons are chains
        for x in self.ground:
            self.assertIn(frozenset([x]), chains)
        # Verify all found sets are indeed chains
        for c in chains:
            self.assertTrue(is_chain(c, self.subset_le))

    def test_find_maximal_chains(self):
        """Test finding maximal chains in powerset poset."""
        max_chains = find_maximal_chains(self.ground, self.subset_le)
        expected_chains = [
            frozenset([frozenset(), frozenset({1}), frozenset({1, 2})]),
            frozenset([frozenset(), frozenset({2}), frozenset({1, 2})]),
        ]
        self.assertEqual(len(max_chains), 2)
        for ec in expected_chains:
            self.assertIn(ec, max_chains)


class TestZornLemma(unittest.TestCase):
    """Test maximal elements and Zorn lemma ascending search."""

    def test_maximal_elements_single_top(self):
        """Test finding unique maximal element in powerset."""
        ground = [frozenset(), frozenset({1}), frozenset({2}), frozenset({1, 2})]
        le = {(a, b) for a in ground for b in ground if a.issubset(b)}
        max_elems = find_maximal_elements(ground, le)
        self.assertEqual(max_elems, {frozenset({1, 2})})

    def test_maximal_elements_multiple(self):
        """Test finding multiple maximal elements in proper subset poset."""
        ground = [
            frozenset(),
            frozenset({1}),
            frozenset({2}),
            frozenset({3}),
            frozenset({1, 2}),
            frozenset({1, 3}),
            frozenset({2, 3}),
        ]
        le = {(a, b) for a in ground for b in ground if a.issubset(b)}
        max_elems = find_maximal_elements(ground, le)
        expected = {frozenset({1, 2}), frozenset({1, 3}), frozenset({2, 3})}
        self.assertEqual(max_elems, expected)

    def test_is_maximal_element(self):
        """Test predicate is_maximal_element."""
        ground = [1, 2, 3]
        le = {(a, b) for a in ground for b in ground if a <= b}
        self.assertFalse(is_maximal_element(1, ground, le))
        self.assertFalse(is_maximal_element(2, ground, le))
        self.assertTrue(is_maximal_element(3, ground, le))

    def test_zorn_find_maximal_from_bottom(self):
        """Test constructive Zorn search reaching a maximal element."""
        ground = [
            frozenset(),
            frozenset({1}),
            frozenset({2}),
            frozenset({1, 2}),
            frozenset({1, 3}),
        ]
        le = {(a, b) for a in ground for b in ground if a.issubset(b)}
        max_el = zorn_find_maximal(ground, le, start=frozenset({1}))
        self.assertTrue(is_maximal_element(max_el, ground, le))
        self.assertIn(max_el, {frozenset({1, 2}), frozenset({1, 3})})

    def test_zorn_find_maximal_empty_ground(self):
        """Test Zorn search on empty ground raises ValueError."""
        with self.assertRaises(ValueError):
            zorn_find_maximal([], set())


class TestWellOrdering(unittest.TestCase):
    """Test well-ordering construction and verification."""

    def test_find_least_element(self):
        """Test finding least element in subset."""
        elements = [10, 20, 30]
        le = {(a, b) for a in elements for b in elements if a <= b}
        self.assertEqual(find_least_element([20, 30], le), 20)
        self.assertEqual(find_least_element([10, 30], le), 10)
        self.assertIsNone(find_least_element([], le))

    def test_is_well_ordering_natural_numbers(self):
        """Test verification of well-ordering on finite set."""
        elements = [3, 1, 4, 15, 9]
        le = {(a, b) for a in elements for b in elements if a <= b}
        self.assertTrue(is_well_ordering(elements, le))

    def test_is_well_ordering_empty_and_singleton(self):
        """Test well-ordering on empty set and singleton."""
        self.assertTrue(is_well_ordering([], set()))
        self.assertTrue(is_well_ordering([42], {(42, 42)}))

    def test_well_order_from_choice(self):
        """Test transfinite construction of well-ordering from choice function."""
        elements = ["gamma", "alpha", "beta", "delta"]
        # Use lexicographical min as choice
        chooser = lambda s: sorted(s)[0]
        le = well_order_from_choice(elements, choice_fn=chooser)
        self.assertTrue(is_well_ordering(elements, le))
        self.assertTrue(is_linear_order(elements, le))

        # Check that alpha is the least element
        self.assertEqual(find_least_element(elements, le), "alpha")

    def test_verify_well_ordering_theorem(self):
        """Test high-level well-ordering theorem verifier."""
        elements = [100, 2, 55, 14, 999]
        self.assertTrue(verify_well_ordering_theorem(elements))
        self.assertTrue(verify_well_ordering_theorem([]))


class TestTukeyLemma(unittest.TestCase):
    """Test finite character properties and Tukey's Lemma."""

    def test_is_finite_character_at_most_k_subsets(self):
        """Test that subsets of size at most 2 form a collection of finite character."""
        base_set = frozenset({1, 2, 3, 4})
        # F is collection of all subsets of base_set of size <= 2
        f_collection = {
            s for s in [frozenset()] + [frozenset({x}) for x in base_set]
            + [frozenset({x, y}) for x in base_set for y in base_set if x != y]
        }
        self.assertTrue(is_finite_character(f_collection, base_set))

    def test_is_finite_character_fails_for_non_hereditary(self):
        """Test that non-hereditary collection is not of finite character."""
        base_set = frozenset({1, 2})
        # Collection containing {1, 2} but missing {1}
        f_collection = {frozenset(), frozenset({2}), frozenset({1, 2})}
        self.assertFalse(is_finite_character(f_collection, base_set))

    def test_find_maximal_element_tukey(self):
        """Test finding maximal element in a collection of finite character."""
        base_set = frozenset({1, 2, 3})
        # Subsets of size <= 2
        f_collection = {
            s for s in [frozenset()] + [frozenset({x}) for x in base_set]
            + [frozenset({x, y}) for x in base_set for y in base_set if x != y]
        }
        max_s = find_maximal_element_tukey(f_collection)
        self.assertIsNotNone(max_s)
        self.assertEqual(len(max_s), 2)

    def test_verify_tukey_lemma(self):
        """Test verification of Tukey's Lemma on finite character collections."""
        base_set = frozenset({"a", "b", "c"})
        # Subsets not containing both 'a' and 'b'
        f_collection = {
            s for s in [
                frozenset(),
                frozenset({"a"}),
                frozenset({"b"}),
                frozenset({"c"}),
                frozenset({"a", "c"}),
                frozenset({"b", "c"}),
            ]
        }
        self.assertTrue(is_finite_character(f_collection, base_set))
        self.assertTrue(verify_tukey_lemma(f_collection, base_set))


class TestJechModuleExports(unittest.TestCase):
    """Test that all choice and Zorn functions are exported from jech package."""

    def test_imports_from_jech(self):
        """Verify direct importability from top-level jech package."""
        import jech

        expected_symbols = [
            "choice_function",
            "has_choice_function",
            "cartesian_product_choice",
            "is_partial_order",
            "is_linear_order",
            "is_chain",
            "upper_bounds",
            "is_chain_bounded",
            "find_all_chains",
            "find_maximal_chains",
            "is_maximal_element",
            "find_maximal_elements",
            "zorn_find_maximal",
            "find_least_element",
            "is_well_ordering",
            "well_order_from_choice",
            "verify_well_ordering_theorem",
            "is_finite_character",
            "find_maximal_element_tukey",
            "verify_tukey_lemma",
        ]
        for sym in expected_symbols:
            self.assertTrue(
                hasattr(jech, sym),
                f"Symbol {sym} not exported in jech top-level package",
            )


if __name__ == "__main__":
    unittest.main()
