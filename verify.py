#!/usr/bin/env python3

import os
import sys

# List of file extensions to check
FILE_EXTENSIONS = ['.py', '.md', '.txt']

# List of directories to exclude
EXCLUDE_DIRS = ['.git', 'tickets']

def verify_files(directory):
    """Verify the syntax and structure of files in the given directory."""
    for root, dirs, files in os.walk(directory):
        # Skip excluded directories
        dirs[:] = [d for d in dirs if d not in EXCLUDE_DIRS]

        for file in files:
            file_path = os.path.join(root, file)
            file_ext = os.path.splitext(file)[1]

            # Check if the file extension is in the list of extensions to check
            if file_ext in FILE_EXTENSIONS:
                try:
                    with open(file_path, 'r') as f:
                        content = f.read()
                    # Add specific checks for different file types here
                    if file_ext == '.py':
                        # Basic syntax check for Python files
                        compile(content, file_path, 'exec')
                    print(f"Verified: {file_path}")
                except Exception as e:
                    print(f"Error in {file_path}: {e}", file=sys.stderr)
                    sys.exit(1)

def run_unit_tests(directory):
    """Run test suite to verify module behavior and exports."""
    import unittest
    test_dir = os.path.join(directory, 'tests')
    if os.path.isdir(test_dir):
        print(f"Running unit tests in {test_dir}...")
        loader = unittest.defaultTestLoader
        suite = loader.discover(test_dir, pattern='test_*.py')
        runner = unittest.TextTestRunner(verbosity=1)
        result = runner.run(suite)
        if not result.wasSuccessful():
            print("Unit tests failed!", file=sys.stderr)
            sys.exit(1)
        print(f"Unit tests passed ({result.testsRun} tests executed).")

if __name__ == "__main__":
    jech_dir = os.path.dirname(os.path.abspath(__file__))
    verify_files(jech_dir)
    run_unit_tests(jech_dir)
    print("All files verified successfully.")
