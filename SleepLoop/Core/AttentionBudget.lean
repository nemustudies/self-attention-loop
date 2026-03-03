/-
  SleepLoop/Core/AttentionBudget.lean

  Corollary 13 (cor:budget): Attention budget constraint.
  Under any simplex map phi, sum_tau a_t(tau) = 1 at every step.
  For |X| = n elements, mean attention = 1/n.
  Level: 𝒜.
-/
import SleepLoop.Defs.Observation

open Finset BigOperators

/-! ## Attention Budget Constraint -/

variable {n : ℕ}

/-- cor:budget: Attention weights sum to 1 under any simplex map. -/
theorem attention_sum_one
    {φ : (Fin n → ℝ) → (Fin n → ℝ)} [SimplexMap φ]
    (S σ b : Fin n → ℝ) :
    ∑ i : Fin n, observe φ S σ b i = 1 := by
  unfold observe
  exact SimplexMap.sum_one _

/-- cor:budget (mean): Mean attention per element = 1/n. -/
theorem attention_mean
    {φ : (Fin n → ℝ) → (Fin n → ℝ)} [SimplexMap φ]
    [NeZero n]
    (S σ b : Fin n → ℝ) :
    (∑ i : Fin n, observe φ S σ b i) / n = 1 / (n : ℝ) := by
  rw [attention_sum_one S σ b]

/-- cor:budget (dilution): Adding an element strictly decreases mean attention. -/
theorem attention_dilution (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (n + 1) < 1 / n := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn1_pos : (0 : ℝ) < (↑(n + 1) : ℝ) := Nat.cast_pos.mpr (by omega)
  apply div_lt_div_of_pos_left one_pos (Nat.cast_pos.mpr hn)
    (by exact_mod_cast (show n < n + 1 by omega))
