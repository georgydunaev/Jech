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

if __name__ == "__main__":
    verify_files('/botworkspace/Jech')
    print("All files verified successfully.")
