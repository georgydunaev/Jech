"""Mostowski Collapsing Theorem and Ordinal Rank.

This module provides algorithmic implementations and verification tools for:
- Well-founded relations and minimal elements
- Extensional relations
- Transitive closure TC(x)
- Inductive ordinal rank function: rank(x) = sup { rank(y) + 1 | y E x }
- Mostowski collapsing isomorphism pi: (A, E) onto a transitive set (M, in)
- Von Neumann ordinals and transitive set verification
"""

from typing import Any, Callable, Dict, FrozenSet, Iterable, List, Optional, Set, Tuple, Union

RelationType = Union[Iterable[Tuple[Any, Any]], Callable[[Any, Any], bool]]


def _normalize_relation(domain: Iterable[Any], relation: RelationType) -> Set[Tuple[Any, Any]]:
    """Convert a relation over domain into a set of pairs (y, x) meaning y E x."""
    dom_set = set(domain)
    if callable(relation):
        return {(y, x) for x in dom_set for y in dom_set if relation(y, x)}
    else:
        return {(y, x) for (y, x) in relation if y in dom_set and x in dom_set}


def predecessors(x: Any, domain: Iterable[Any], relation: RelationType) -> Set[Any]:
    """Return the set of immediate E-predecessors of x: { y in domain | (y, x) in E }."""
    rel = _normalize_relation(domain, relation)
    return {y for (y, target) in rel if target == x}


def is_minimal(x: Any, subset: Iterable[Any], relation: RelationType) -> bool:
    """Check if x is an E-minimal element of subset (no y in subset has y E x)."""
    sub = set(subset)
    if x not in sub:
        return False
    rel = _normalize_relation(sub, relation)
    for (y, target) in rel:
        if target == x and y in sub:
            return False
    return True


def find_minimal_element(subset: Iterable[Any], relation: RelationType) -> Optional[Any]:
    """Find an E-minimal element of a non-empty subset, or None if cyclic."""
    sub = set(subset)
    if not sub:
        return None
    rel = _normalize_relation(sub, relation)
    for x in sub:
        if all(y not in sub for (y, target) in rel if target == x):
            return x
    return None


def is_well_founded(domain: Iterable[Any], relation: RelationType) -> bool:
    """Check if relation E is well-founded on domain.

    A relation is well-founded on domain if every non-empty subset of domain
    contains an E-minimal element.
    """
    dom = set(domain)
    if not dom:
        return True
    rel = _normalize_relation(dom, relation)

    # Iteratively remove minimal elements (topological elimination)
    remaining = set(dom)
    while remaining:
        minimal = None
        for x in remaining:
            if all(y not in remaining for (y, target) in rel if target == x):
                minimal = x
                break
        if minimal is None:
            return False
        remaining.remove(minimal)
    return True


def is_extensional(domain: Iterable[Any], relation: RelationType) -> bool:
    """Check if relation E is extensional on domain.

    A relation is extensional if distinct elements have distinct predecessor sets:
    forall x, y in domain, pred(x) == pred(y) implies x == y.
    """
    dom = list(domain)
    rel = _normalize_relation(dom, relation)
    preds: Dict[Any, FrozenSet[Any]] = {}
    for x in dom:
        p = frozenset(y for (y, target) in rel if target == x)
        preds[x] = p

    for i in range(len(dom)):
        for j in range(i + 1, len(dom)):
            x, y = dom[i], dom[j]
            if preds[x] == preds[y]:
                return False
    return True


def transitive_closure_relation(domain: Iterable[Any], relation: RelationType) -> Set[Tuple[Any, Any]]:
    """Compute the transitive closure E+ of relation E on domain."""
    dom = set(domain)
    rel = _normalize_relation(dom, relation)
    tc = set(rel)
    changed = True
    while changed:
        changed = False
        new_edges = set()
        for (a, b) in tc:
            for (c, d) in tc:
                if b == c and (a, d) not in tc:
                    new_edges.add((a, d))
        if new_edges:
            tc.update(new_edges)
            changed = True
    return tc


def transitive_closure(x: Any, domain: Iterable[Any], relation: RelationType) -> Set[Any]:
    """Compute TC(x) = { y in domain | (y, x) in E+ }."""
    tc_rel = transitive_closure_relation(domain, relation)
    return {y for (y, target) in tc_rel if target == x}


def rank(domain: Iterable[Any], relation: RelationType) -> Dict[Any, int]:
    """Compute the ordinal rank of every element in domain.

    rank(x) = sup { rank(y) + 1 | (y, x) in E }.

    Raises:
        ValueError: If (domain, relation) is not well-founded.
    """
    dom = set(domain)
    if not is_well_founded(dom, relation):
        raise ValueError("Relation is not well-founded; rank is undefined.")

    rel = _normalize_relation(dom, relation)
    ranks: Dict[Any, int] = {}
    remaining = set(dom)

    while remaining:
        # Pick an element whose predecessors all have assigned ranks
        ready = None
        for x in remaining:
            preds = {y for (y, target) in rel if target == x}
            if preds.issubset(ranks.keys()):
                ready = x
                break
        if ready is None:
            raise ValueError("Cycle detected during rank computation.")
        preds = {y for (y, target) in rel if target == ready}
        if not preds:
            ranks[ready] = 0
        else:
            ranks[ready] = max(ranks[y] + 1 for y in preds)
        remaining.remove(ready)

    return ranks


def mostowski_collapse(
    domain: Iterable[Any],
    relation: RelationType
) -> Tuple[Dict[Any, FrozenSet[Any]], FrozenSet[FrozenSet[Any]]]:
    """Compute the Mostowski collapse isomorphism pi: (A, E) onto (M, in).

    pi(x) = { pi(y) | (y, x) in E }.
    Returns:
        (collapse_map, transitive_set) where:
        collapse_map maps each element of A to its corresponding frozenset in M,
        and transitive_set is the image M = pi[A].

    Raises:
        ValueError: If relation is not well-founded or not extensional.
    """
    dom = set(domain)
    if not is_well_founded(dom, relation):
        raise ValueError("Relation is not well-founded; Mostowski collapse requires well-foundedness.")
    if not is_extensional(dom, relation):
        raise ValueError("Relation is not extensional; Mostowski collapse requires extensionality.")

    rel = _normalize_relation(dom, relation)
    collapse_map: Dict[Any, FrozenSet[Any]] = {}
    remaining = set(dom)

    while remaining:
        ready = None
        for x in remaining:
            preds = {y for (y, target) in rel if target == x}
            if preds.issubset(collapse_map.keys()):
                ready = x
                break
        if ready is None:
            raise ValueError("Cycle detected during Mostowski collapse.")
        preds = {y for (y, target) in rel if target == ready}
        collapsed_val = frozenset(collapse_map[y] for y in preds)
        collapse_map[ready] = collapsed_val
        remaining.remove(ready)

    transitive_set = frozenset(collapse_map.values())
    return collapse_map, transitive_set


def is_transitive_set(m_set: FrozenSet[Any]) -> bool:
    """Check if a set M of frozensets is transitive: forall s in M, s subseteq M."""
    for s in m_set:
        if isinstance(s, (frozenset, set)):
            for elem in s:
                if elem not in m_set:
                    return False
        else:
            return False
    return True


def von_neumann_ordinal(n: int) -> FrozenSet[Any]:
    """Construct the n-th von Neumann ordinal as a nested frozenset.

    0 = empty set
    n + 1 = n union {n}
    """
    if n < 0:
        raise ValueError("Ordinal index must be non-negative.")
    curr: FrozenSet[Any] = frozenset()
    for _ in range(n):
        curr = curr | frozenset([curr])
    return curr


def verify_mostowski_isomorphism(
    domain: Iterable[Any],
    relation: RelationType,
    collapse_map: Dict[Any, FrozenSet[Any]]
) -> bool:
    """Verify that pi = collapse_map satisfies all Mostowski isomorphism conditions:

    1. Injectivity: pi(x) == pi(y) implies x == y.
    2. Relation isomorphism: (y, x) in E iff pi(y) in pi(x).
    3. Transitivity: image M = pi[A] is a transitive set.
    """
    dom = list(domain)
    rel = _normalize_relation(dom, relation)

    # 1. Injectivity
    for i in range(len(dom)):
        for j in range(i + 1, len(dom)):
            x, y = dom[i], dom[j]
            if collapse_map[x] == collapse_map[y]:
                return False

    # 2. Relation isomorphism
    for x in dom:
        for y in dom:
            rel_holds = (y, x) in rel
            membership_holds = collapse_map[y] in collapse_map[x]
            if rel_holds != membership_holds:
                return False

    # 3. Transitivity of image
    m_set = frozenset(collapse_map.values())
    if not is_transitive_set(m_set):
        return False

    return True


class WellFoundedStructure:
    """Encapsulation of a relational structure (A, E) for rank and collapse operations."""

    def __init__(self, domain: Iterable[Any], relation: RelationType):
        self.domain = set(domain)
        self.relation = _normalize_relation(self.domain, relation)

    def is_well_founded(self) -> bool:
        return is_well_founded(self.domain, self.relation)

    def is_extensional(self) -> bool:
        return is_extensional(self.domain, self.relation)

    def rank(self) -> Dict[Any, int]:
        return rank(self.domain, self.relation)

    def transitive_closure(self, x: Any) -> Set[Any]:
        return transitive_closure(x, self.domain, self.relation)

    def collapse(self) -> Tuple[Dict[Any, FrozenSet[Any]], FrozenSet[FrozenSet[Any]]]:
        return mostowski_collapse(self.domain, self.relation)

    def verify_collapse(self) -> bool:
        cmap, _ = self.collapse()
        return verify_mostowski_isomorphism(self.domain, self.relation, cmap)
