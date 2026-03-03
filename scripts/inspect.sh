#!/usr/bin/env bash
# inspect.sh — Automated dependency and structure report for Lean reviewers.
# Run from the SleepLoop project root: ./scripts/inspect.sh
set -e

cd "$(dirname "$0")/.."

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║          SleepLoop — Formalization Inspection Report        ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# ── 1. Project stats ─────────────────────────────────────────────
echo "=== Project Stats ==="
LEAN_FILES=$(find SleepLoop/ -name '*.lean' ! -path '*/.lake/*' | wc -l)
TOTAL_LINES=$(find SleepLoop/ -name '*.lean' ! -path '*/.lake/*' -exec cat {} + | wc -l)
echo "  Lean files:     $LEAN_FILES"
echo "  Lines of code:  ~$TOTAL_LINES"
echo ""

# ── 2. Sorry / axiom / True audit ────────────────────────────────
echo "=== Proof Integrity ==="

# Match sorry as a tactic (line-start), same pattern as validate.sh
SORRY_COUNT=$(grep -rn --include='*.lean' '^ *sorry' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | wc -l)
echo "  Files with sorry:       $SORRY_COUNT"

AXIOM_COUNT=$(grep -rn --include='*.lean' '^axiom ' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | wc -l)
echo "  Custom axiom decls:     $AXIOM_COUNT"

TRUE_COUNT=$(grep -rn --include='*.lean' ': True ' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | grep -v -- '--' | wc -l)
echo "  True placeholders:      $TRUE_COUNT"
echo ""

# ── 3. Mathlib imports ────────────────────────────────────────────
echo "=== Mathlib Imports (direct, by area) ==="
echo ""
echo "  These are the Mathlib modules this project directly imports."
echo "  Each line = one import statement somewhere in the project."
echo ""

# Collect unique imports, sort, group by top-level area
grep -rh --include='*.lean' '^import Mathlib\.' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' \
  | sed 's/import //' \
  | sort -u > /tmp/sleeploop_mathlib_imports.txt

# Group by Mathlib.X
prev_area=""
while IFS= read -r imp; do
  area=$(echo "$imp" | cut -d. -f1-2)
  if [ "$area" != "$prev_area" ]; then
    [ -n "$prev_area" ] && echo ""
    echo "  ── $area ──"
    prev_area="$area"
  fi
  echo "    $imp"
done < /tmp/sleeploop_mathlib_imports.txt

IMPORT_COUNT=$(wc -l < /tmp/sleeploop_mathlib_imports.txt)
echo ""
echo "  Total unique Mathlib imports: $IMPORT_COUNT"
echo ""

# ── 4. Mathlib imports per project file ───────────────────────────
echo "=== Mathlib Imports per File (heaviest first) ==="
echo ""
echo "  Files that directly import Mathlib (not via other project files)."
echo ""

grep -rl --include='*.lean' '^import Mathlib\.' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' \
  | while read -r f; do
      count=$(grep -c '^import Mathlib\.' "$f")
      echo "$count $f"
    done \
  | sort -rn \
  | head -20 \
  | while read -r count file; do
      printf "  %2d imports  %s\n" "$count" "$file"
    done
echo ""

# ── 5. Key Mathlib lemma usage ────────────────────────────────────
echo "=== Key Mathlib Lemmas & Techniques ==="
echo ""
echo "  Frequently referenced Mathlib names in proof terms and doc strings."
echo "  (Approximate counts via pattern matching — includes comments.)"
echo ""

# Search for common Mathlib identifiers used in proofs
# We look for known heavyweight lemmas
declare -A CATEGORIES
CATEGORIES=(
  ["Topology/Compactness"]="isCompact|IsCompact|compactSpace|CompactSpace"
  ["Topology/Convergence"]="[Tt]endsto|Filter\.Tendsto|atTop|nhds|eventually|Filter\.Eventually"
  ["Convexity"]="convexHull|Convex\.combination|starConvex|convex_"
  ["Analysis/Norms"]="norm_|nnnorm|dist_|edist_"
  ["Analysis/Inner Products"]="inner_|real_inner|InnerProductSpace"
  ["Analysis/Calculus"]="HasDerivAt|hasDerivAt|IntervalIntegral|integral_|FundThmCalculus|deriv_"
  ["Algebra/BigOperators"]="Finset\.sum|Finset\.sup|Finset\.inf|BigOperators|∑|∏"
  ["Special Functions"]="Real\.exp|Real\.log|rpow|NNReal"
  ["Order/Lattice"]="sup'|inf'|ciSup|ciInf|sSup|sInf"
  ["Measure Theory"]="MeasureTheory|Integrable|intervalIntegrable"
)

for cat in "Topology/Compactness" "Topology/Convergence" "Convexity" "Analysis/Norms" \
           "Analysis/Inner Products" "Analysis/Calculus" "Algebra/BigOperators" \
           "Special Functions" "Order/Lattice" "Measure Theory"; do
  pattern="${CATEGORIES[$cat]}"
  count=$(grep -rn --include='*.lean' -E "$pattern" SleepLoop/ 2>/dev/null \
    | grep -v '\.lake' | grep -v '^.*:.*--' | wc -l)
  if [ "$count" -gt 0 ]; then
    printf "  %-28s %4d references\n" "$cat" "$count"
  fi
done
echo ""

# ── 6. Proof technique highlights ────────────────────────────────
echo "=== Notable Proof Techniques ==="
echo ""

# Check for FTC / integration proofs
FTC=$(grep -rl --include='*.lean' 'intervalIntegral\|FundThmCalculus\|integral_eq_sub' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | head -5)
if [ -n "$FTC" ]; then
  echo "  Fundamental Theorem of Calculus:"
  echo "$FTC" | sed 's/^/    /'
fi

# Check for compactness arguments
COMPACT=$(grep -rl --include='*.lean' 'isCompact\|IsCompact\|compactSpace' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | head -5)
if [ -n "$COMPACT" ]; then
  echo "  Compactness arguments:"
  echo "$COMPACT" | sed 's/^/    /'
fi

# Check for Lyapunov / monotone convergence
LYAP=$(grep -rl --include='*.lean' 'tendsto_of_monotone\|MonotoneConvergence\|tendsto_atTop_ciInf\|squeeze_zero' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | head -5)
if [ -n "$LYAP" ]; then
  echo "  Monotone/squeeze convergence:"
  echo "$LYAP" | sed 's/^/    /'
fi

# Check for convex hull proofs
HULL=$(grep -rl --include='*.lean' 'convexHull_min\|subset_convexHull\|convex_convexHull' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | head -5)
if [ -n "$HULL" ]; then
  echo "  Convex hull invariance:"
  echo "$HULL" | sed 's/^/    /'
fi

echo ""

# ── 7. Theorem count ─────────────────────────────────────────────
echo "=== Theorem-like Declarations ==="

THEOREMS=$(grep -rn --include='*.lean' '^theorem \|^lemma \|^private theorem \|^private lemma ' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | wc -l)
DEFS=$(grep -rn --include='*.lean' '^def \|^noncomputable def \|^private def \|^private noncomputable def ' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | wc -l)
INSTANCES=$(grep -rn --include='*.lean' '^instance ' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | wc -l)
STRUCTURES=$(grep -rn --include='*.lean' '^structure \|^class ' SleepLoop/ 2>/dev/null \
  | grep -v '\.lake' | wc -l)

echo "  theorems/lemmas:  $THEOREMS"
echo "  definitions:      $DEFS"
echo "  instances:        $INSTANCES"
echo "  structures/classes: $STRUCTURES"
echo ""

# ── 8. MainTheorem isolation check ───────────────────────────────
echo "=== MainTheorem.lean Isolation ==="
echo ""
echo "  Imports in MainTheorem.lean:"
grep '^import ' SleepLoop/MainTheorem.lean | sed 's/^/    /'
echo ""
if grep -q '^import SleepLoop\.' SleepLoop/MainTheorem.lean 2>/dev/null; then
  echo "  WARNING: MainTheorem.lean imports project files!"
else
  echo "  PASS: Only Mathlib imports (no project dependencies)"
fi
echo ""

# ── Summary ──────────────────────────────────────────────────────
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  Summary: $LEAN_FILES files, ~$TOTAL_LINES lines, $IMPORT_COUNT Mathlib imports"
printf "║  sorry=%d  axiom=%d  True=%d\n" "$SORRY_COUNT" "$AXIOM_COUNT" "$TRUE_COUNT"
echo "╚══════════════════════════════════════════════════════════════╝"

rm -f /tmp/sleeploop_mathlib_imports.txt
