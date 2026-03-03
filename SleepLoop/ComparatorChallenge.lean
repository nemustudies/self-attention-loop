import SleepLoop.MainTheorem

/-- Comparator challenge target. The `sorry` is intentional: this file declares the
    theorem to be proved so that `comparator` can verify `ProofOfMainTheorem.lean`
    proves exactly this statement. This file is never imported by any proof file. -/
theorem mainTheorem : StatementOfTheorem := by sorry
