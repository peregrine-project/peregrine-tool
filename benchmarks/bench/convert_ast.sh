#!/bin/bash
# Convert old LambdaBox AST format to new PAst format
# Old: (env main)
# New: (Untyped env (Some main))

if [ $# -lt 1 ]; then
    echo "Usage: $0 <input.ast> [output.ast]"
    exit 1
fi

INPUT="$1"
OUTPUT="${2:-${INPUT%.ast}_new.ast}"

# Read the file content
content=$(cat "$INPUT")

# The old format is ((decls...) main_term)
# We need to transform it to (Untyped (decls...) (Some main_term))
# Use sed to wrap appropriately

# First, find the split between env and main
# The structure is (env main) where env is a list of declarations
# env ends with )))) and main starts after that

# Simple approach: wrap the whole thing
echo "(Untyped $content)" | sed 's/(Untyped (\(.*\)) \(.*\))$/(Untyped (\1) (Some \2))/' > "$OUTPUT"

echo "Converted $INPUT -> $OUTPUT"
