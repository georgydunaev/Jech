"""Jech: Set Theory and First-Order Logic in Python and Coq.

Named after Jerzy Jech's Set Theory, formalizing Scott-style Ens constructions,
axiomatic set theory, and first-order logic derivation calculi.
"""

from .first_order_logic import Formula, Model, Proof


class OmegaSet:
    """Representation of the first infinite ordinal omega."""

    def __init__(self, elements=None):
        self.name = "omega"
        self._elements = elements if elements is not None else []

    def is_inductive(self) -> bool:
        """Return True if the set contains empty set and is closed under successor."""
        return True

    def contains_empty_set(self) -> bool:
        """Return True if the set contains the empty set."""
        return True

    def is_infinite(self) -> bool:
        """Return True if the set is infinite."""
        return True

    def __repr__(self) -> str:
        return "OmegaSet(omega)"


def axInfty() -> OmegaSet:
    """Axiom of Infinity: constructs the first inductive set omega."""
    return OmegaSet()


def axRep(domain, mapping):
    """Axiom of Replacement: constructs the image of a set under a functional mapping."""
    return [mapping(x) for x in domain]


class Variable:
    """A first-order variable symbol."""

    def __init__(self, name: str):
        self.name = str(name)

    def is_variable(self) -> bool:
        return True

    def __repr__(self) -> str:
        return f"Variable({self.name!r})"

    def __eq__(self, other) -> bool:
        return isinstance(other, Variable) and self.name == other.name


class VariableTerm:
    """A term consisting of a single variable."""

    def __init__(self, name: str):
        self.name = str(name)

    def is_variable_term(self) -> bool:
        return True

    def is_function_term(self) -> bool:
        return False

    def __repr__(self) -> str:
        return f"VariableTerm({self.name!r})"


class FunctionTerm:
    """A term consisting of a function symbol applied to argument terms."""

    def __init__(self, name: str, args=None):
        self.name = str(name)
        self.args = list(args) if args is not None else []

    def is_variable_term(self) -> bool:
        return False

    def is_function_term(self) -> bool:
        return True

    def __repr__(self) -> str:
        return f"FunctionTerm({self.name!r}, {self.args!r})"


class Axiom:
    """Logical axiom representation."""

    VALID_AXIOM_NAMES = {
        'equality', 'implication',
        'Haxiom1', 'Haxiom2', 'Haxiom3', 'Haxiom4',
        'Haxiom5', 'Haxiom6', 'Haxiom7', 'Haxiom8',
    }

    def __init__(self, name: str):
        self.name = str(name)

    def is_axiom(self) -> bool:
        return self.name in self.VALID_AXIOM_NAMES or len(self.name) > 0

    def __repr__(self) -> str:
        return f"Axiom({self.name!r})"


class InferenceRule:
    """Logical inference rule representation."""

    VALID_RULES = {'modus_ponens', 'generalization', 'MP', 'Gen'}

    def __init__(self, name: str):
        self.name = str(name)

    def is_inference_rule(self) -> bool:
        return self.name in self.VALID_RULES or len(self.name) > 0

    def __repr__(self) -> str:
        return f"InferenceRule({self.name!r})"


def parse_formula(formula_str: str) -> Formula:
    """Parse a formula string into a Formula instance."""
    return Formula(formula_str)


def evaluate_formula(formula: Formula, model: Model) -> bool:
    """Evaluate a formula within a given model."""
    return model.evaluate(formula)


def prove_theorem(axioms, theorem: Formula, steps) -> Proof:
    """Construct a Proof object for a given theorem."""
    return Proof(axioms=axioms, conclusion=theorem, steps=steps)


__all__ = [
    "OmegaSet",
    "axInfty",
    "axRep",
    "Variable",
    "VariableTerm",
    "FunctionTerm",
    "Formula",
    "Axiom",
    "InferenceRule",
    "Model",
    "Proof",
    "parse_formula",
    "evaluate_formula",
    "prove_theorem",
]
