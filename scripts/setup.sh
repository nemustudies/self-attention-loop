#!/usr/bin/env bash
set -e

FULL=false
if [ "$1" = "--full" ]; then
  FULL=true
fi

echo "=== SleepLoop Setup ==="
if $FULL; then
  echo "  Mode: full (Lean + Python + lean4checker + comparator)"
else
  echo "  Mode: lean-only (pass --full for Python + lean4checker)"
fi
echo ""

# ---------------------------------------------------------------------------
# 1. Lean 4 (via elan)
# ---------------------------------------------------------------------------
echo "[1/4] Lean 4..."

if command -v elan &>/dev/null; then
  echo "  elan found: $(elan --version 2>/dev/null | head -1)"
  echo "  lean: $(lean --version 2>/dev/null | head -1)"
else
  echo "  Installing elan (Lean version manager)..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
  echo "  Done. lean: $(lean --version 2>/dev/null | head -1)"
fi

# ---------------------------------------------------------------------------
# 2. Python packages (--full only)
# ---------------------------------------------------------------------------
echo "[2/4] Python packages..."

if ! $FULL; then
  echo "  SKIP (pass --full to install numpy + torch)"
else
  if command -v python3 &>/dev/null; then
    PYTHON=python3
  elif command -v python &>/dev/null; then
    PYTHON=python
  else
    echo "  SKIP: Python not found. Install Python 3.8+ for numerical verification."
    PYTHON=""
  fi

  if [ -n "$PYTHON" ]; then
    echo "  $PYTHON: $($PYTHON --version 2>&1)"
    echo "  Installing numpy..."
    $PYTHON -m pip install --quiet numpy
    echo "  Installing torch (large download, ~2GB)..."
    $PYTHON -m pip install --quiet torch
    echo "  Done."
  fi
fi

# ---------------------------------------------------------------------------
# 3. lean4checker (--full only)
# ---------------------------------------------------------------------------
echo "[3/4] lean4checker..."

if ! $FULL; then
  echo "  SKIP (pass --full to install)"
else
  TOOLCHAIN=$(cat SleepLoop/lean-toolchain 2>/dev/null || cat lean-toolchain 2>/dev/null || echo "")

  if [ -d "lean4checker" ]; then
    echo "  Already cloned at ./lean4checker"
  elif [ -n "$TOOLCHAIN" ]; then
    echo "  Cloning and building for $TOOLCHAIN..."
    git clone --quiet https://github.com/leanprover/lean4checker
    cd lean4checker
    TAG=$(echo "$TOOLCHAIN" | sed 's|leanprover/lean4:||')
    git checkout --quiet "$TAG" 2>/dev/null || echo "  Note: tag $TAG not found, using master"
    lake build
    cd ..
    echo "  Done."
  else
    echo "  SKIP: No lean-toolchain found. Run from the project root."
  fi
fi

# ---------------------------------------------------------------------------
# 4. comparator (--full only)
# ---------------------------------------------------------------------------
echo "[4/4] comparator..."

if ! $FULL; then
  echo "  SKIP (pass --full to install)"
else
  if [ -d "comparator" ]; then
    echo "  Already cloned at ./comparator"
  else
    echo "  Cloning and building comparator..."
    git clone --quiet https://github.com/leanprover/comparator
    cd comparator
    lake build
    cd ..
    echo "  Done."
  fi

  # Check for landrun + lean4export
  if ! command -v landrun &>/dev/null; then
    echo "  Note: landrun not found. Install from https://github.com/Zouuup/landrun"
  fi
  if ! command -v lean4export &>/dev/null; then
    echo "  Note: lean4export not found. Install from https://github.com/leanprover/lean4export"
  fi
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=== Setup complete ==="
echo ""
echo "Next steps:"
echo "  lake build              # Build the formalization (~2740 jobs)"
echo "  ./scripts/validate.sh   # Run full validation"
if $FULL; then
  echo "  python verify_bounds.py               # Numerical bound verification"
  echo "  python check_proofs.py paper/sleep_paper.tex  # LaTeX structural check"
fi
