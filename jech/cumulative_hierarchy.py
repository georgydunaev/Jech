"""Cumulative Hierarchy V_alpha, Foundation, and Montague-Levy Reflection.

Theoretical references:
    - Jerzy Jech, Set Theory (3rd Millennium Edition):
      * Chapter 2: Ordinals and Cumulative Hierarchy (V_alpha)
      * Chapter 6: The Axiom of Regularity / Foundation (Theorem 6.2)
      * Chapter 12: The Reflection Principle (Theorem 12.14)
"""

from itertools import chain, combinations
from typing import Dict, FrozenSet, List, Optional, Set, Tuple, Union


# =========================================================================
# 1. POWERSET AND CUMULATIVE HIERARCHY STAGES
# =========================================================================

EMPTY_SET: FrozenSet = frozenset()


def powerset(s: FrozenSet) -> FrozenSet[FrozenSet]:
    """Compute powerset P(s) as a frozenset of frozensets."""
    items = list(s)
    subsets = chain.from_iterable(combinations(items, r) for r in range(len(items) + 1))
    return frozenset(frozenset(subset) for subset in subsets)


_STAGE_CACHE: Dict[int, FrozenSet[FrozenSet]] = {}


def v_stage(n: int) -> FrozenSet[FrozenSet]:
    """Compute cumulative stage V_n for finite ranks (0 <= n <= 4).

    V_0 = empty
    V_{n+1} = Power(V_n)
    """
    if n < 0:
        raise ValueError("Stage index must be non-negative")
    if n in _STAGE_CACHE:
        return _STAGE_CACHE[n]

    if n == 0:
        res: FrozenSet[FrozenSet] = frozenset()
    else:
        prev = v_stage(n - 1)
        res = powerset(prev)

    _STAGE_CACHE[n] = res
    return res


def generate_stages(max_n: int = 4) -> Dict[int, FrozenSet[FrozenSet]]:
    """Generate all cumulative stages from V_0 up to V_{max_n}."""
    return {n: v_stage(n) for n in range(max_n + 1)}


# =========================================================================
# 2. TRANSITIVITY AND MONOTONICITY VERIFICATION
# =========================================================================

def is_transitive_stage(stage: FrozenSet[FrozenSet]) -> bool:
    """Verify that stage is transitive: for all x in stage, x is subset of stage."""
    for x in stage:
        if not x.issubset(stage):
            return False
    return True


def verify_monotonicity(stages: Dict[int, FrozenSet[FrozenSet]]) -> bool:
    """Verify cumulative monotonicity: i <= j implies V_i subset of V_j."""
    indices = sorted(stages.keys())
    for idx, i in enumerate(indices):
        for j in indices[idx:]:
            if not stages[i].issubset(stages[j]):
                return False
    return True


# =========================================================================
# 3. SET RANK COMPUTATION
# =========================================================================

def set_rank(x: FrozenSet) -> int:
    """Compute ordinal rank of hereditarily finite set x.

    rank(empty) = 0
    rank(x) = 1 + max { rank(y) : y in x }
    """
    if not x:
        return 0
    return 1 + max(set_rank(y) for y in x)


def least_stage_containing(x: FrozenSet, max_stage: int = 4) -> Optional[int]:
    """Find the least n such that x in V_n."""
    for n in range(max_stage + 1):
        if x in v_stage(n):
            return n
    return None


def von_neumann_ordinal_set(n: int) -> FrozenSet:
    """Generate von Neumann ordinal n as a hereditarily finite frozenset.

    0 = empty
    n+1 = n union {n}
    """
    if n < 0:
        raise ValueError("Ordinal must be non-negative")
    res = EMPTY_SET
    for i in range(n):
        res = res | frozenset([res])
    return res


# =========================================================================
# 4. TRANSITIVE CLOSURE AND FOUNDATION (ACYCLICITY)
# =========================================================================

def transitive_closure_set(x: FrozenSet) -> FrozenSet[FrozenSet]:
    """Compute transitive closure TC(x) = x union Union { TC(y) : y in x }."""
    tc: Set[FrozenSet] = set(x)
    frontier = list(x)
    while frontier:
        curr = frontier.pop()
        for y in curr:
            if y not in tc:
                tc.add(y)
                frontier.append(y)
    return frozenset(tc)


def is_well_founded_set(x: FrozenSet) -> bool:
    """Check epsilon-foundation (acyclicity) for set x.

    Builds membership relation over TC(x) union {x} and verifies no cycles.
    """
    domain = list(transitive_closure_set(x) | frozenset([x]))
    # DFS cycle detection
    visited: Dict[FrozenSet, int] = {}  # 0: unvisited, 1: visiting, 2: visited

    def has_cycle(u: FrozenSet) -> bool:
        visited[u] = 1
        for v in u:
            if v in domain:
                status = visited.get(v, 0)
                if status == 1:
                    return True
                if status == 0 and has_cycle(v):
                    return True
        visited[u] = 2
        return False

    for node in domain:
        if visited.get(node, 0) == 0:
            if has_cycle(node):
                return False
    return True


def find_in_minimal_element(subset: FrozenSet[FrozenSet]) -> Optional[FrozenSet]:
    """Find in-minimal element m in non-empty subset S such that m intersection S is empty."""
    if not subset:
        return None
    # An element of minimal rank in subset is always in-minimal
    return min(subset, key=set_rank)


def verify_foundation_on_stage(stage: FrozenSet[FrozenSet]) -> bool:
    """Verify regularity on stage: every non-empty subset S has an in-minimal element."""
    # Test on power of small subsets
    for x in stage:
        if x:
            m = find_in_minimal_element(x)
            if m is None or (m & x):
                return False
    return True


# =========================================================================
# 5. FIRST-ORDER FORMULAS AND DELTA_0 ABSOLUTENESS
# =========================================================================

class SetFormula:
    """Abstract base class for first-order set-theoretic formulas."""
    pass


class AtomEq(SetFormula):
    """Atomic equality formula: x = y."""

    def __init__(self, x: str, y: str):
        self.x = str(x)
        self.y = str(y)

    def __repr__(self) -> str:
        return f"AtomEq({self.x!r}, {self.y!r})"


class AtomIn(SetFormula):
    """Atomic membership formula: x in y."""

    def __init__(self, x: str, y: str):
        self.x = str(x)
        self.y = str(y)

    def __repr__(self) -> str:
        return f"AtomIn({self.x!r}, {self.y!r})"


class FNot(SetFormula):
    """Negation: not phi."""

    def __init__(self, phi: SetFormula):
        self.phi = phi

    def __repr__(self) -> str:
        return f"FNot({self.phi!r})"


class FAnd(SetFormula):
    """Conjunction: phi and psi."""

    def __init__(self, phi: SetFormula, psi: SetFormula):
        self.phi = phi
        self.psi = psi

    def __repr__(self) -> str:
        return f"FAnd({self.phi!r}, {self.psi!r})"


class FOr(SetFormula):
    """Disjunction: phi or psi."""

    def __init__(self, phi: SetFormula, psi: SetFormula):
        self.phi = phi
        self.psi = psi

    def __repr__(self) -> str:
        return f"FOr({self.phi!r}, {self.psi!r})"


class FImp(SetFormula):
    """Implication: phi implies psi."""

    def __init__(self, phi: SetFormula, psi: SetFormula):
        self.phi = phi
        self.psi = psi

    def __repr__(self) -> str:
        return f"FImp({self.phi!r}, {self.psi!r})"


class FBoundedAll(SetFormula):
    """Bounded universal quantifier: forall var in bound_var, phi."""

    def __init__(self, var: str, bound_var: str, phi: SetFormula):
        self.var = str(var)
        self.bound_var = str(bound_var)
        self.phi = phi

    def __repr__(self) -> str:
        return f"FBoundedAll({self.var!r}, {self.bound_var!r}, {self.phi!r})"


class FBoundedEx(SetFormula):
    """Bounded existential quantifier: exists var in bound_var, phi."""

    def __init__(self, var: str, bound_var: str, phi: SetFormula):
        self.var = str(var)
        self.bound_var = str(bound_var)
        self.phi = phi

    def __repr__(self) -> str:
        return f"FBoundedEx({self.var!r}, {self.bound_var!r}, {self.phi!r})"


class FAll(SetFormula):
    """Unbounded universal quantifier: forall var in domain, phi."""

    def __init__(self, var: str, phi: SetFormula):
        self.var = str(var)
        self.phi = phi

    def __repr__(self) -> str:
        return f"FAll({self.var!r}, {self.phi!r})"


class FEx(SetFormula):
    """Unbounded existential quantifier: exists var in domain, phi."""

    def __init__(self, var: str, phi: SetFormula):
        self.var = str(var)
        self.phi = phi

    def __repr__(self) -> str:
        return f"FEx({self.var!r}, {self.phi!r})"


def is_delta_0(phi: SetFormula) -> bool:
    """Check if formula is Delta_0 (contains only bounded quantifiers)."""
    if isinstance(phi, (AtomEq, AtomIn)):
        return True
    if isinstance(phi, FNot):
        return is_delta_0(phi.phi)
    if isinstance(phi, (FAnd, FOr, FImp)):
        return is_delta_0(phi.phi) and is_delta_0(phi.psi)
    if isinstance(phi, (FBoundedAll, FBoundedEx)):
        return is_delta_0(phi.phi)
    if isinstance(phi, (FAll, FEx)):
        return False
    return False


def evaluate_formula(
    phi: SetFormula,
    env: Dict[str, FrozenSet],
    domain: FrozenSet[FrozenSet]
) -> bool:
    """Evaluate satisfaction of formula phi in structure with domain under assignment env."""
    if isinstance(phi, AtomEq):
        return env[phi.x] == env[phi.y]

    if isinstance(phi, AtomIn):
        return env[phi.x] in env[phi.y]

    if isinstance(phi, FNot):
        return not evaluate_formula(phi.phi, env, domain)

    if isinstance(phi, FAnd):
        return evaluate_formula(phi.phi, env, domain) and evaluate_formula(phi.psi, env, domain)

    if isinstance(phi, FOr):
        return evaluate_formula(phi.phi, env, domain) or evaluate_formula(phi.psi, env, domain)

    if isinstance(phi, FImp):
        if not evaluate_formula(phi.phi, env, domain):
            return True
        return evaluate_formula(phi.psi, env, domain)

    if isinstance(phi, FBoundedAll):
        bound_set = env[phi.bound_var]
        for val in bound_set:
            new_env = dict(env)
            new_env[phi.var] = val
            if not evaluate_formula(phi.phi, new_env, domain):
                return False
        return True

    if isinstance(phi, FBoundedEx):
        bound_set = env[phi.bound_var]
        for val in bound_set:
            new_env = dict(env)
            new_env[phi.var] = val
            if evaluate_formula(phi.phi, new_env, domain):
                return True
        return False

    if isinstance(phi, FAll):
        for val in domain:
            new_env = dict(env)
            new_env[phi.var] = val
            if not evaluate_formula(phi.phi, new_env, domain):
                return False
        return True

    if isinstance(phi, FEx):
        for val in domain:
            new_env = dict(env)
            new_env[phi.var] = val
            if evaluate_formula(phi.phi, new_env, domain):
                return True
        return False

    raise TypeError(f"Unknown formula type: {type(phi)}")


# =========================================================================
# 6. MONTAGUE-LEVY REFLECTION PRINCIPLE
# =========================================================================

def verify_delta_0_reflection(
    phi: SetFormula,
    env: Dict[str, FrozenSet],
    stage_small: FrozenSet[FrozenSet],
    stage_large: FrozenSet[FrozenSet]
) -> bool:
    """Verify that Delta_0 formula reflects between transitive substructure and larger stage."""
    if not is_delta_0(phi):
        raise ValueError("Formula must be Delta_0")
    val_small = evaluate_formula(phi, env, stage_small)
    val_large = evaluate_formula(phi, env, stage_large)
    return val_small == val_large


def is_witness_closed(
    phi: SetFormula,
    var: str,
    env: Dict[str, FrozenSet],
    stage: FrozenSet[FrozenSet],
    universe: FrozenSet[FrozenSet]
) -> bool:
    """Tarski-Vaught criterion: if exists v in universe phi(v), then exists v' in stage phi(v')."""
    exists_in_universe = False
    for val in universe:
        new_env = dict(env)
        new_env[var] = val
        if evaluate_formula(phi, new_env, universe):
            exists_in_universe = True
            break

    if not exists_in_universe:
        return True

    for val in stage:
        new_env = dict(env)
        new_env[var] = val
        if evaluate_formula(phi, new_env, universe):
            return True
    return False


def find_reflection_stages(
    phi: SetFormula,
    env: Dict[str, FrozenSet],
    stages: Dict[int, FrozenSet[FrozenSet]],
    target_stage: int = 4
) -> List[int]:
    """Find all stage indices k <= target_stage such that phi^{V_k} iff phi^{V_target}."""
    target_val = evaluate_formula(phi, env, stages[target_stage])
    reflecting_indices = []
    for k, st in sorted(stages.items()):
        # Check that environment elements are contained in stage k
        if all(val in st for val in env.values()):
            if evaluate_formula(phi, env, st) == target_val:
                reflecting_indices.append(k)
    return reflecting_indices
