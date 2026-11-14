"""Axiom of Choice, Zorn's Lemma, and Well-Ordering Theorem.

This module provides algorithmic implementations and verification tools for:
- Choice functions on finite and structured set families
- Cartesian product non-emptiness under choice
- Partially ordered sets, chain finders, upper bounds, and maximal elements
- Constructive Zorn's lemma maximal element search
- Well-ordering relations and transfinite/iterative well-ordering construction
- Teichmuller-Tukey finite character test and maximal element verification
"""

import itertools
from typing import Any, Callable, Dict, FrozenSet, Iterable, List, Optional, Set, Tuple, Union

RelationType = Union[Iterable[Tuple[Any, Any]], Callable[[Any, Any], bool]]


def _normalize_relation(domain: Iterable[Any], relation: RelationType) -> Set[Tuple[Any, Any]]:
    """Convert a relation over domain into a set of pairs (x, y) meaning x <= y."""
    dom_set = set(domain)
    if callable(relation):
        return {(x, y) for x in dom_set for y in dom_set if relation(x, y)}
    else:
        return {(x, y) for (x, y) in relation if x in dom_set and y in dom_set}


# =========================================================================
# 1. CHOICE FUNCTIONS AND CARTESIAN PRODUCTS
# =========================================================================

def choice_function(
    collection: Iterable[Iterable[Any]],
    strategy: Optional[Callable[[Iterable[Any]], Any]] = None,
) -> Dict[FrozenSet[Any], Any]:
    """Construct a choice function mapping each non-empty set in collection to an element.

    Parameters:
        collection: An iterable of set-like iterables.
        strategy: Optional selection callable; defaults to min if sortable, else first item.

    Returns:
        A dictionary mapping each frozenset to its chosen element.

    Raises:
        ValueError: If any member of collection is empty.
    """
    result: Dict[FrozenSet[Any], Any] = {}
    for item in collection:
        s = frozenset(item)
        if not s:
            raise ValueError("Axiom of Choice requires all members to be non-empty")
        if strategy is not None:
            chosen = strategy(s)
        else:
            try:
                chosen = min(s)
            except TypeError:
                chosen = next(iter(s))
        if chosen not in s:
            raise ValueError("Strategy selected an element not belonging to the set")
        result[s] = chosen
    return result


def has_choice_function(collection: Iterable[Iterable[Any]]) -> bool:
    """Return True if collection has a choice function (every member is non-empty)."""
    for item in collection:
        s = frozenset(item)
        if not s:
            return False
    return True


def cartesian_product_choice(*sets: Iterable[Any]) -> Tuple[Any, ...]:
    """Extract a choice tuple from a sequence of non-empty sets.

    Parameters:
        sets: Variable number of non-empty iterables.

    Returns:
        A tuple containing one element chosen from each respective set.

    Raises:
        ValueError: If any factor set is empty.
    """
    choice_list: List[Any] = []
    for idx, s_iter in enumerate(sets):
        s = list(s_iter)
        if not s:
            raise ValueError(f"Cartesian product factor at index {idx} is empty")
        choice_list.append(s[0])
    return tuple(choice_list)


# =========================================================================
# 2. PARTIALLY ORDERED SETS, CHAINS, AND UPPER BOUNDS
# =========================================================================

def is_partial_order(domain: Iterable[Any], le_relation: RelationType) -> bool:
    """Check if le_relation is a partial order (reflexive, transitive, antisymmetric)."""
    dom = set(domain)
    rel = _normalize_relation(dom, le_relation)

    # Reflexivity: forall x in domain, (x, x) in rel
    for x in dom:
        if (x, x) not in rel:
            return False

    # Antisymmetry: forall x, y in domain, x <= y and y <= x implies x == y
    for (x, y) in rel:
        if x != y and (y, x) in rel:
            return False

    # Transitivity: forall x, y, z in domain, x <= y and y <= z implies x <= z
    for (x, y) in rel:
        for (y2, z) in rel:
            if y == y2 and (x, z) not in rel:
                return False

    return True


def is_linear_order(domain: Iterable[Any], le_relation: RelationType) -> bool:
    """Check if le_relation is a linear order (partial order and total)."""
    dom = list(domain)
    if not is_partial_order(dom, le_relation):
        return False
    rel = _normalize_relation(dom, le_relation)
    for i in range(len(dom)):
        for j in range(i + 1, len(dom)):
            x, y = dom[i], dom[j]
            if (x, y) not in rel and (y, x) not in rel:
                return False
    return True


def is_chain(subset: Iterable[Any], le_relation: RelationType) -> bool:
    """Check if subset is a chain under le_relation (every pair is comparable)."""
    sub = list(subset)
    rel = _normalize_relation(sub, le_relation)
    for i in range(len(sub)):
        for j in range(i + 1, len(sub)):
            x, y = sub[i], sub[j]
            if (x, y) not in rel and (y, x) not in rel:
                return False
    return True


def upper_bounds(
    chain: Iterable[Any],
    domain: Iterable[Any],
    le_relation: RelationType,
) -> Set[Any]:
    """Return the set of all upper bounds for chain within domain."""
    dom = set(domain)
    ch = set(chain)
    rel = _normalize_relation(dom, le_relation)
    bounds: Set[Any] = set()
    for u in dom:
        if all((c, u) in rel for c in ch):
            bounds.add(u)
    return bounds


def is_chain_bounded(domain: Iterable[Any], le_relation: RelationType) -> bool:
    """Check if every chain in domain has at least one upper bound in domain."""
    dom = set(domain)
    chains = find_all_chains(dom, le_relation)
    for ch in chains:
        if not upper_bounds(ch, dom, le_relation):
            return False
    return True


def find_all_chains(domain: Iterable[Any], le_relation: RelationType) -> List[FrozenSet[Any]]:
    """Enumerate all chains (subsets where every pair is comparable) in domain."""
    dom = list(domain)
    rel = _normalize_relation(dom, le_relation)
    chains: List[FrozenSet[Any]] = [frozenset()]

    for r in range(1, len(dom) + 1):
        for combo in itertools.combinations(dom, r):
            if is_chain(combo, rel):
                chains.append(frozenset(combo))
    return chains


def find_maximal_chains(domain: Iterable[Any], le_relation: RelationType) -> List[FrozenSet[Any]]:
    """Find all inclusion-maximal chains in the poset."""
    all_ch = find_all_chains(domain, le_relation)
    ch_set = set(all_ch)
    maximal_chains: List[FrozenSet[Any]] = []
    for ch in all_ch:
        if not any(ch < other for other in ch_set):
            maximal_chains.append(ch)
    return maximal_chains


# =========================================================================
# 3. MAXIMAL ELEMENTS AND ZORN'S LEMMA
# =========================================================================

def is_maximal_element(x: Any, domain: Iterable[Any], le_relation: RelationType) -> bool:
    """Check if x is a maximal element of domain under le_relation."""
    dom = set(domain)
    if x not in dom:
        return False
    rel = _normalize_relation(dom, le_relation)
    for y in dom:
        if y != x and (x, y) in rel:
            return False
    return True


def find_maximal_elements(domain: Iterable[Any], le_relation: RelationType) -> Set[Any]:
    """Find all maximal elements in the poset (domain, le_relation)."""
    dom = set(domain)
    rel = _normalize_relation(dom, le_relation)
    maximal: Set[Any] = set()
    for x in dom:
        if not any(y != x and (x, y) in rel for y in dom):
            maximal.add(x)
    return maximal


def zorn_find_maximal(
    domain: Iterable[Any],
    le_relation: RelationType,
    start: Optional[Any] = None,
) -> Any:
    """Constructive Zorn search: ascend along upper bounds of chains to a maximal element.

    Parameters:
        domain: The poset elements.
        le_relation: The partial order relation.
        start: Optional starting element.

    Returns:
        A maximal element in the poset.

    Raises:
        ValueError: If domain is empty or not a partial order.
    """
    dom = list(domain)
    if not dom:
        raise ValueError("Cannot apply Zorn lemma to an empty poset")
    if not is_partial_order(dom, le_relation):
        raise ValueError("The provided relation is not a partial order")

    rel = _normalize_relation(dom, le_relation)
    current = start if start is not None and start in dom else dom[0]

    visited: Set[Any] = {current}
    while True:
        strict_successors = [y for y in dom if y != current and (current, y) in rel]
        if not strict_successors:
            return current
        next_elem = None
        for candidate in strict_successors:
            if candidate not in visited:
                next_elem = candidate
                break
        if next_elem is None:
            return current
        visited.add(next_elem)
        current = next_elem


# =========================================================================
# 4. WELL-ORDERING THEOREM
# =========================================================================

def find_least_element(subset: Iterable[Any], le_relation: RelationType) -> Optional[Any]:
    """Find the least element of subset under le_relation, or None if empty."""
    sub = set(subset)
    if not sub:
        return None
    rel = _normalize_relation(sub, le_relation)
    for m in sub:
        if all((m, x) in rel for x in sub):
            return m
    return None


def is_well_ordering(domain: Iterable[Any], le_relation: RelationType) -> bool:
    """Check if le_relation is a well-ordering on domain.

    A relation is a well-ordering if it is a linear order and every non-empty
    subset has a least element.
    """
    dom = list(domain)
    if not is_linear_order(dom, le_relation):
        return False
    rel = _normalize_relation(dom, le_relation)

    for r in range(1, len(dom) + 1):
        for combo in itertools.combinations(dom, r):
            if find_least_element(combo, rel) is None:
                return False
    return True


def well_order_from_choice(
    domain: Iterable[Any],
    choice_fn: Optional[Callable[[Set[Any]], Any]] = None,
) -> Set[Tuple[Any, Any]]:
    """Construct a well-ordering on domain using an iterative choice operator.

    Parameters:
        domain: Elements to be well-ordered.
        choice_fn: Optional choice operator picking an element from remaining set.

    Returns:
        A set of pairs (x, y) defining the well-ordering relation <=.
    """
    remaining = set(domain)
    ordered_sequence: List[Any] = []

    while remaining:
        if choice_fn is not None:
            chosen = choice_fn(remaining)
        else:
            try:
                chosen = min(remaining)
            except TypeError:
                chosen = next(iter(remaining))
        if chosen not in remaining:
            raise ValueError("Choice operator returned element outside remaining set")
        ordered_sequence.append(chosen)
        remaining.remove(chosen)

    index_map = {elem: idx for idx, elem in enumerate(ordered_sequence)}
    rel: Set[Tuple[Any, Any]] = set()
    for x in ordered_sequence:
        for y in ordered_sequence:
            if index_map[x] <= index_map[y]:
                rel.add((x, y))
    return rel


def verify_well_ordering_theorem(domain: Iterable[Any]) -> bool:
    """Verify that domain can be well-ordered by constructing and validating a well-order."""
    dom = list(domain)
    rel = well_order_from_choice(dom)
    return is_well_ordering(dom, rel)


# =========================================================================
# 5. TEICHMULLER-TUKEY LEMMA (FINITE CHARACTER)
# =========================================================================

def is_finite_character(
    collection: Iterable[Iterable[Any]],
    universe: Iterable[Any],
) -> bool:
    """Test if collection of subsets of universe has finite character.

    A collection F has finite character if for every S subset universe,
    S in F if and only if every finite subset of S is in F.
    """
    u = set(universe)
    f_set = {frozenset(s) for s in collection}

    all_subsets = [frozenset(combo) for r in range(len(u) + 1) for combo in itertools.combinations(u, r)]

    for s in all_subsets:
        all_finite_subs_in_f = True
        for r in range(len(s) + 1):
            for sub_combo in itertools.combinations(s, r):
                if frozenset(sub_combo) not in f_set:
                    all_finite_subs_in_f = False
                    break
            if not all_finite_subs_in_f:
                break

        in_f = s in f_set
        if in_f != all_finite_subs_in_f:
            return False

    return True


def find_maximal_element_tukey(collection: Iterable[Iterable[Any]]) -> Optional[FrozenSet[Any]]:
    """Find an inclusion-maximal element in collection."""
    f_list = [frozenset(s) for s in collection]
    if not f_list:
        return None
    f_set = set(f_list)
    for s in f_list:
        if not any(s < other for other in f_set):
            return s
    return None


def verify_tukey_lemma(
    collection: Iterable[Iterable[Any]],
    universe: Iterable[Any],
) -> bool:
    """Verify Tukey's Lemma: non-empty family of finite character has a maximal element."""
    col = list(collection)
    if not col:
        return True
    if not is_finite_character(col, universe):
        return False
    maximal = find_maximal_element_tukey(col)
    return maximal is not None
