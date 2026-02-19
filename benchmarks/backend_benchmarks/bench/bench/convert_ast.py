#!/usr/bin/env python3
"""Convert old LambdaBox AST format to new PAst format.

Old format: (env term)
New format: (Untyped env (Some term))

Where env is a list of declarations like ((kn decl) (kn decl) ...)
and term is the main term.
"""

import sys
import re

def find_matching_paren(s, start):
    """Find the index of the closing paren matching the one at start."""
    count = 1
    i = start + 1
    while i < len(s) and count > 0:
        if s[i] == '(':
            count += 1
        elif s[i] == ')':
            count -= 1
        i += 1
    return i - 1

def convert_ast(content):
    """Convert old AST format to new PAst format."""
    content = content.strip()

    # The old format is (env main_term)
    # env is a list of declarations: ((kn decl) (kn decl) ...)
    # main_term is the expression after the env

    if not content.startswith('('):
        raise ValueError("AST must start with (")

    # Find the end of the env (list of declarations)
    # The env starts at position 1 and is a list of pairs
    # We need to find where the list ends and the main term begins

    # Find matching ) for the opening (
    end = find_matching_paren(content, 0)

    if end != len(content) - 1:
        raise ValueError(f"Unexpected content after main expression at position {end}")

    # Inside the outer parens, we have: env main_term
    # env is (...) and main_term is (...)
    inner = content[1:-1].strip()

    # Find the env (first element)
    if not inner.startswith('('):
        raise ValueError("Expected env to start with (")

    env_end = find_matching_paren(inner, 0)
    env = inner[:env_end+1]

    # The rest is the main term
    main_term = inner[env_end+1:].strip()

    if not main_term:
        # No main term
        return f"(Untyped {env} None)"
    else:
        return f"(Untyped {env} (Some {main_term}))"

def main():
    if len(sys.argv) < 2:
        print("Usage: convert_ast.py <input.ast> [output.ast]")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else input_file.replace('.ast', '_new.ast')

    with open(input_file, 'r') as f:
        content = f.read()

    try:
        converted = convert_ast(content)
        with open(output_file, 'w') as f:
            f.write(converted)
        print(f"Converted {input_file} -> {output_file}")
    except Exception as e:
        print(f"Error converting {input_file}: {e}")
        sys.exit(1)

if __name__ == '__main__':
    main()
