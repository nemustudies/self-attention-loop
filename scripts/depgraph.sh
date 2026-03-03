#!/usr/bin/env bash
# depgraph.sh — Generate Lean import dependency graph.
# Outputs DOT format to stdout. Pipe to graphviz to render:
#   ./scripts/depgraph.sh > deps.dot
#   ./scripts/depgraph.sh | dot -Tpng -o deps.png    # requires graphviz
#   ./scripts/depgraph.sh | dot -Tsvg -o deps.svg
set -e
cd "$(dirname "$0")/.."

echo "digraph SleepLoop {"
echo '  rankdir=BT;'
echo '  node [shape=box, fontsize=10, fontname="monospace"];'
echo '  edge [color="#666666"];'
echo ""

# Color nodes by directory
echo "  // Verification + MainTheorem (red = audit surface)"
echo '  "Verification" [style=filled, fillcolor="#ffcccc"];'
echo '  "ProofOfMainTheorem" [style=filled, fillcolor="#ffcccc"];'
echo '  "MainTheorem" [style=filled, fillcolor="#ffcccc", penwidth=2];'
echo ""

find SleepLoop/ -name '*.lean' ! -path '*/.lake/*' | sort | while read -r file; do
  # Get module name: SleepLoop/Core/Convergence.lean -> Core.Convergence
  mod=$(echo "$file" | sed 's|^SleepLoop/||; s|\.lean$||; s|/|.|g')

  # Short name for display
  short=$(echo "$mod" | sed 's|^SleepLoop\.||')
  [ "$short" = "$mod" ] && short="$mod"

  # Color by directory
  dir=$(echo "$short" | cut -d. -f1)
  case "$dir" in
    Defs)              color="#e8f4e8" ;;  # green
    Core)              color="#e8e8f4" ;;  # blue
    Rigidity)          color="#f4e8f4" ;;  # purple
    Sleep)             color="#f4f4e8" ;;  # yellow
    CaptureInertness)  color="#f4e8e8" ;;  # pink
    Appendix)          color="#e8f4f4" ;;  # cyan
    *)                 color="#ffffff" ;;
  esac

  # Skip if already colored above
  case "$short" in
    Verification|ProofOfMainTheorem|MainTheorem) ;;
    *) echo "  \"$short\" [style=filled, fillcolor=\"$color\"];" ;;
  esac

  # Extract SleepLoop imports and emit edges
  grep '^import SleepLoop\.' "$file" 2>/dev/null | while read -r line; do
    dep=$(echo "$line" | sed 's|^import SleepLoop\.||')
    echo "  \"$short\" -> \"$dep\";"
  done
done

echo ""
echo "  // Legend"
echo '  subgraph cluster_legend {'
echo '    label="Legend"; style=rounded; fontsize=10;'
echo '    node [shape=box, fontsize=8, width=1.2];'
echo '    "Defs/" [style=filled, fillcolor="#e8f4e8"];'
echo '    "Core/" [style=filled, fillcolor="#e8e8f4"];'
echo '    "Rigidity/" [style=filled, fillcolor="#f4e8f4"];'
echo '    "Sleep/" [style=filled, fillcolor="#f4f4e8"];'
echo '    "CaptureInertness/" [style=filled, fillcolor="#f4e8e8"];'
echo '    "Appendix/" [style=filled, fillcolor="#e8f4f4"];'
echo '    "Audit surface" [style=filled, fillcolor="#ffcccc"];'
echo '  }'
echo "}"
