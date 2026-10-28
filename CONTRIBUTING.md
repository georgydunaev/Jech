# Contributing to Jech

## Project Overview

The Jech library is a Coq library focused on set theory and first-order logic. It includes various parts covering ZFC axioms, exercises from Jech's "Set Theory" book, and experiments with classes. The library is structured into several parts, each with specific goals and definitions.

## Goals

1. Create a self-contained book of first-order logic and ZFC set theory.
2. Solve exercises from Jech's "Set Theory".
3. Re-use proofs from Metamath.

## Structure

The library is divided into several parts:

1. **Part I**: Large isolated part of the `/coq-contribs/zfc/` library and proofs of some axioms of ZFC.
2. **Part II**: Development of the classic ZFC theory with exercises from Jech's "Set Theory" and "Introduction to Set Theory" books.
3. **Part III**: Development of formulas and derivations for first-order logic.
4. **Part IV**: Experiments with classes and many theorems about them.
5. **Part V**: Translation of Metamath theorems.


## How to Contribute

## Reporting Issues

If you encounter any bugs or have suggestions for improvements, please open an issue on the GitHub repository. When reporting an issue, please include:

- A clear and descriptive title
- A detailed description of the problem or suggestion
- Steps to reproduce the issue (if applicable)
- Any relevant code snippets or error messages
- The version of the library you are using
- Your operating system and environment details

### Issue Templates

To make it easier to report issues, the repository includes issue templates. Please use the appropriate template when opening a new issue.


If you encounter any bugs or have suggestions for improvements, please open an issue on the GitHub repository. When reporting an issue, please include:

- A clear and descriptive title
- A detailed description of the problem or suggestion
- Steps to reproduce the issue (if applicable)
- Any relevant code snippets or error messages

## Creating Pull Requests

To contribute code to the Jech library, please follow these steps:

1. **Fork the repository**: Fork the repository to your own GitHub account.
2. **Clone the repository**: Clone the repository to your local machine.
3. **Create a new branch**: Create a new branch for your changes.
4. **Make your changes**: Make your changes to the code.
5. **Test your changes**: Test your changes to ensure they work as expected.
6. **Commit your changes**: Commit your changes with descriptive commit messages.
7. **Push your changes**: Push your changes to your fork.
8. **Open a pull request**: Open a pull request on the main repository.

### Pull Request Guidelines

- **Descriptive title**: Use a clear and descriptive title for your pull request.
- **Detailed description**: Include a detailed description of the changes you have made.
- **Related issues**: Link to any related issues in the description.
- **Testing**: Include information about how you tested your changes.
- **Documentation**: Update the documentation if necessary.

### Code Review

All pull requests will be reviewed by the maintainers. Please be patient and responsive to any feedback or requests for changes.


To contribute code to the Jech library, please follow these steps:

1. Fork the repository and clone it to your local machine.
2. Create a new branch for your changes.
3. Make your changes and commit them with descriptive commit messages.
4. Push your changes to your fork.
5. Open a pull request on the main repository.

## Code Style Guidelines

To maintain consistency and readability, please follow these code style guidelines:

### General Guidelines

1. **Variable and Function Names**:
   - Use clear and descriptive names
   - Follow the existing naming conventions
   - Use camelCase for variables and functions
   - Use PascalCase for class and type names

2. **Indentation and Formatting**:
   - Use 2 spaces for indentation
   - Keep lines of code under 80 characters
   - Use consistent spacing around operators and after commas

3. **Comments**:
   - Use single-line comments (`//`) for brief explanations
   - Use multi-line comments (`/* ... */`) for more detailed explanations
   - Avoid redundant comments that simply restate the code

4. **Code Organization**:
   - Group related functions and variables together
   - Follow the existing code structure and organization

### Coq-Specific Guidelines

1. **Proofs and Definitions**:
   - Use clear and descriptive names for proofs and definitions
   - Include comments to explain complex or non-obvious code
   - Follow the existing proof style and organization

2. **Tactics**:
   - Use consistent and readable tactics
   - Avoid overly complex or nested tactics
   - Use the `Set` command to simplify expressions when appropriate

3. **Documentation**:
   - Include documentation for new modules and functions
   - Use the `Document` command to generate documentation
   - Follow the existing documentation style and organization


To maintain consistency and readability, please follow these code style guidelines:

- Use clear and descriptive variable and function names.
- Include comments to explain complex or non-obvious code.
- Follow the existing code structure and organization.
- Use consistent indentation and formatting.

#### Specific Guidelines:

1. **Variable and Function Names**:
   - Use camelCase for variable and function names (e.g., `myVariable`, `calculateSum`).
   - Use PascalCase for class and type names (e.g., `MyClass`, `MyType`).

2. **Indentation and Formatting**:
   - Use 2 spaces for indentation.
   - Keep lines of code under 80 characters.
   - Use consistent spacing around operators and after commas.

3. **Comments**:
   - Use single-line comments (`//`) for brief explanations.
   - Use multi-line comments (`/* ... */`) for more detailed explanations.
   - Avoid redundant comments that simply restate the code.

4. **Code Organization**:
   - Group related functions and variables together.
   - Use modules to organize code into logical units.
   - Follow the existing project structure and naming conventions.

#### Example:

```coq
// Example of a well-formatted function in Coq
Definition sum (n: nat) : nat := 
  match n with
  | O => O
  | S m => S (sum m)
  end.
```

For more details, refer to the existing codebase and the [Coq Documentation](https://coq.inria.fr/documentation).

To maintain consistency and readability, please follow these code style guidelines:

- Use clear and descriptive variable and function names.
- Include comments to explain complex or non-obvious code.
- Follow the existing code structure and organization.
- Use consistent indentation and formatting.

### Review Process

All contributions will be reviewed by the maintainers. Please be patient and responsive to any feedback or requests for changes.

## Review Process

All contributions will be reviewed by the maintainers. Please be patient and responsive to any feedback or requests for changes.

## License

By contributing to the Jech library, you agree that your contributions will be licensed under the [MIT License](LICENSE).

By contributing to the Jech library, you agree that your contributions will be licensed under the [MIT License](LICENSE).
