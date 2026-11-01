# Jech Roadmap

## Current Status

The Jech library has made significant progress in its first five passes of autonomous delegation. The core mathematical content — including the Axiom of Infinity and Axiom of Replacement — has been internally proven using the `sup` constructor, and the Python API is functional for key use cases.

## Near-Term Priorities (Pass 2/5)

1. **Polish Rough Edges**: Review the existing codebase and identify any rough edges that need polishing. This includes:
   - Cleaning up informal proofs in `src/proofs/axRep_axInfty.ML` and `test_axRep_axInfty.ML`
   - Making the Python module imports more robust and error-resistant
   - Ensuring all Coq files compile cleanly with `make check`

2. **Add Comprehensive Documentation**: Add comprehensive documentation for the existing codebase to make it easier for others to understand and contribute. Key documentation targets:
   - `README.md`: Already enhanced with full mathematical/software contents
   - `DOCS.md`: Detailed definitions, theorems, Python API, and usage examples
   - `ROADMAP.md`: This file — long-term vision and priority tracking
   - `THEOREMS_INDEX.md`: High-level index of definitions and theorems
   - Inline code comments in all `.ML` and `.v` files

3. **Identify New Sub-Problems**: Identify any new sub-problems that need to be addressed and create new tickets in the `tickets/` directory. Priority areas:
   - Internal proofs for remaining ZFC axioms (Union, Power Set, Regularity, Choice) within the `Ens` framework
   - Decidability and `eq_fo` structural equality decision procedure for `Fo` formulas
   - Free variable tracking and capture-avoiding substitution for `Fo`
   - Translation `Fo → Formula` into the Hilbert-style syntax of `Part_III.v`

4. **Automated Testing**: Ensure that automated tests are in place to verify the correctness and robustness of the codebase. Specific actions:
   - Create a `tests/` directory with comprehensive test files
   - Add `test_main.py` to test the main functionality
   - Add tests for key definitions and theorems (axInfty, axRep, Formula, Model, Proof)
   - Set up continuous integration to run tests automatically on each commit (`.gitlab-ci.yml` already configured for `make check`)

5. **Community Engagement**: Engage with the community to gather feedback and suggestions for further improvements. Actions:
   - Update `CONTRIBUTING.md` with clear contribution guidelines
   - Add a `LICENSE` file if not present
   - Create a `README` badge showing build status
   - Document how to build, test, and contribute

## Future Enhancements (Pass 3/5 and Beyond)

- **Feature X**: Implement a new feature that enhances the functionality of the repository. Potential ideas:
  - Decision procedure for formula equivalence
  - Interactive proof automation tactics
  - Integration with external provers (e.g., Metamath, Isabelle)

- **Performance Optimization**: Optimize the performance of the existing codebase to improve efficiency. Areas:
  - Coq proof term size reduction
  - Python API overhead minimization
  - Sup-constructor computation optimization

- **Security Review**: Conduct a thorough security review to identify and address any potential vulnerabilities. This is less critical for a formal math library but important for:
  - Safe execution of user-provided Coq scripts
  - Sandboxing Python bindings
  - Dependency management

## Long-Term Vision (Pass 4/5+)

- **ZFC Development**: Complete the internal proof of all ZFC axioms within the `Ens`/`sup` framework, moving from partial (Infinity, Replacement, Extensionality, Pairing, Union) to full (including Power Set, Regularity, Choice).
- **Higher-Order Extensions**: Extend the library with higher-order logic capabilities, allowing more expressive proofs and definitions.
- **Decision Procedures**: Implement decision procedures for fragments of first-order logic, making the library more useful for verification tasks.
- **Ecosystem Integration**: Integrate with other formal libraries (e.g., MathComp, Coq's standard library) and platforms (e.g., GitHub Copilot for Coq, proof assistants).

## Metrics

- Number of internally proven ZFC axioms: 5/9 (Infinity, Replacement, Extensionality, Pairing, Union)
- Number of Coq files checkable: 3/5 (Jech.v, Part_III.v, coq-contribs/zfc/axioms.v)
- Python API coverage: ~60% of core features documented and tested
- Test coverage: Minimal — needs expansion

By following this roadmap, we aim to continuously improve the `Jech` repository and make it more robust, user-friendly, and comprehensive.