#!/usr/bin/env python3

import ast
import os
import sys

# Directory to verify
verify_dir = "/botworkspace/Jech"

# List of file extensions to verify
file_extensions = [".py"]

# List of files to exclude from verification
exclude_files = ["verify.py"]

def verify_syntax(file_path):
    """Verify the syntax of a Python file."""
    try:
        with open(file_path, "r") as file:
            content = file.read()
        ast.parse(content)
        print(f"Syntax OK: {file_path}")
    except SyntaxError as e:
        print(f"Syntax Error in {file_path}: {e}")
    except Exception as e:
        print(f"Error reading {file_path}: {e}")

def main():
    """Main function to verify syntax of Python files in the repository."""
    for root, _, files in os.walk(verify_dir):
        for file in files:
            if any(file.endswith(ext) for ext in file_extensions) and file not in exclude_files:
                file_path = os.path.join(root, file)
                verify_syntax(file_path)

if __name__ == "__main__":
    main()
