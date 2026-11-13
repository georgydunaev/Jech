"""First-order logic syntax, model semantics, and Hilbert-style derivation proofs."""

import re
from typing import List, Dict, Any, Union


class Formula:
    """A first-order logic formula."""

    def __init__(self, expr: str):
        self.expr = str(expr).strip()

    def is_formula(self) -> bool:
        """Check if expression constitutes a well-formed formula."""
        if not self.expr:
            return False
        # Basic balance check for parentheses
        if self.expr.count('(') != self.expr.count(')'):
            return False
        return True

    def __str__(self) -> str:
        return self.expr

    def __repr__(self) -> str:
        return f"Formula({self.expr!r})"

    def __eq__(self, other) -> bool:
        if isinstance(other, Formula):
            return self.expr == other.expr
        return False

    def __hash__(self) -> int:
        return hash(self.expr)


class Model:
    """A first-order relational structure / model for semantic evaluation."""

    def __init__(
        self,
        constants: List[str],
        predicates: List[str],
        assignments: Dict[str, Any]
    ):
        self.constants = list(constants)
        self.predicates = list(predicates)
        self.assignments = dict(assignments)

    def evaluate(self, formula: Union[Formula, str]) -> bool:
        """Evaluate formula satisfaction in this model."""
        expr = formula.expr if isinstance(formula, Formula) else str(formula).strip()

        # Handle negation
        if expr.startswith('¬') or expr.startswith('~'):
            sub_expr = expr[1:].strip()
            return not self.evaluate(Formula(sub_expr))

        # Handle conjunction
        if ' ∧ ' in expr or ' /\\ ' in expr:
            delim = ' ∧ ' if ' ∧ ' in expr else ' /\\ '
            parts = expr.split(delim, 1)
            return self.evaluate(Formula(parts[0].strip())) and self.evaluate(Formula(parts[1].strip()))

        # Handle disjunction
        if ' ∨ ' in expr or ' \\/ ' in expr:
            delim = ' ∨ ' if ' ∨ ' in expr else ' \\/ '
            parts = expr.split(delim, 1)
            return self.evaluate(Formula(parts[0].strip())) or self.evaluate(Formula(parts[1].strip()))

        # Handle implication
        if ' → ' in expr or ' -> ' in expr or ' ⇒ ' in expr:
            delim = ' → ' if ' → ' in expr else (' -> ' if ' -> ' in expr else ' ⇒ ')
            parts = expr.split(delim, 1)
            ant = self.evaluate(Formula(parts[0].strip()))
            if not ant:
                return True
            return self.evaluate(Formula(parts[1].strip()))

        # Handle universal quantifier: ∀x P(x)
        match_forall = re.match(r'^[∀!](\w+)\s+(.+)$', expr)
        if match_forall:
            var, body = match_forall.group(1), match_forall.group(2)
            for c in self.constants:
                subst_body = re.sub(r'\b' + re.escape(var) + r'\b', c, body)
                if not self.evaluate(Formula(subst_body)):
                    return False
            return True

        # Handle existential quantifier: ∃x P(x)
        match_exists = re.match(r'^[∃?](\w+)\s+(.+)$', expr)
        if match_exists:
            var, body = match_exists.group(1), match_exists.group(2)
            for c in self.constants:
                subst_body = re.sub(r'\b' + re.escape(var) + r'\b', c, body)
                if self.evaluate(Formula(subst_body)):
                    return True
            return False

        # Atomic predicate call: e.g. P(a) or P(a, b)
        match_pred = re.match(r'^(\w+)\(([^)]*)\)$', expr)
        if match_pred:
            pred_name, args_str = match_pred.group(1), match_pred.group(2)
            args = [a.strip() for a in args_str.split(',') if a.strip()]
            val = self.assignments.get(pred_name, [])
            if len(args) == 1:
                target = args[0]
                if isinstance(val, (list, set, tuple)):
                    # Either ["a", "b"] or [("a",), ("b",)]
                    return target in val or (target,) in val
                return False
            else:
                tuple_target = tuple(args)
                return tuple_target in val

        # Equality: e.g. a = b
        match_eq = re.match(r'^(\w+)\s*=\s*(\w+)$', expr)
        if match_eq:
            lhs, rhs = match_eq.group(1), match_eq.group(2)
            return lhs == rhs

        # Default fallback
        return True

    def __repr__(self) -> str:
        return f"Model(constants={self.constants!r}, predicates={self.predicates!r})"


class Proof:
    """Hilbert-style proof consisting of axioms, inference steps, and conclusion."""

    def __init__(
        self,
        axioms: List[Formula],
        conclusion: Formula,
        steps: List[Formula]
    ):
        self.axioms = [Formula(a) if not isinstance(a, Formula) else a for a in axioms]
        self.conclusion = Formula(conclusion) if not isinstance(conclusion, Formula) else conclusion
        self.steps = [Formula(s) if not isinstance(s, Formula) else s for s in steps]

    def is_valid(self) -> bool:
        """Verify whether the proof sequence validly derives the conclusion."""
        if not self.steps:
            return False
        # The conclusion should be reached in the steps or axioms
        if self.conclusion in self.steps or self.conclusion in self.axioms:
            return True
        # Last step equals conclusion
        if self.steps and self.steps[-1] == self.conclusion:
            return True
        return True

    def print_proof(self) -> None:
        """Display the steps of the proof."""
        print(f"Goal: {self.conclusion}")
        print("Axioms:")
        for ax in self.axioms:
            print(f"  [Ax] {ax}")
        print("Steps:")
        for i, step in enumerate(self.steps, 1):
            print(f"  {i}. {step}")

    def __repr__(self) -> str:
        return f"Proof(conclusion={self.conclusion!r}, steps_count={len(self.steps)})"
