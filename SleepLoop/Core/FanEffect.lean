/-
  SleepLoop/Core/FanEffect.lean

  Corollary 15 (cor:fan): Retrieval weight dilution (fan effect).
  Under softmax, adding a new impression m_new to M strictly
  decreases every existing retrieval weight.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Retrieval

open Finset BigOperators

/-! ## Fan Effect -/

variable {d : ℕ}

/-- cor:fan: Adding a new element to the softmax denominator
    strictly decreases every existing weight.
    For j ∈ M: softmax(qM'ᵀ)_j < softmax(qMᵀ)_j
    where M' = M ∪ {m_new}. -/
theorem fan_effect
    {n : ℕ} [NeZero n]
    (scores : Fin n → ℝ) (s_new : ℝ) (j : Fin n) :
    let old_denom := ∑ k : Fin n, Real.exp (scores k)
    let new_denom := old_denom + Real.exp s_new
    Real.exp (scores j) / new_denom < Real.exp (scores j) / old_denom := by
  intro old_denom new_denom
  have h_old_pos : 0 < old_denom := softmax_denom_pos scores
  have h_exp_pos : 0 < Real.exp s_new := Real.exp_pos s_new
  have h_new_gt : old_denom < new_denom := lt_add_of_pos_right old_denom h_exp_pos
  exact div_lt_div_of_pos_left (Real.exp_pos (scores j)) h_old_pos h_new_gt

/-- cor:fan: max_j w_j is strictly decreasing as |M| grows. -/
theorem fan_effect_max_weight_decreasing
    {n : ℕ} [NeZero n]
    (scores : Fin n → ℝ) (s_new : ℝ) :
    let old_denom := ∑ k : Fin n, Real.exp (scores k)
    let new_denom := old_denom + Real.exp s_new
    (Finset.sup' Finset.univ Finset.univ_nonempty
      (fun j => Real.exp (scores j) / new_denom)) <
    (Finset.sup' Finset.univ Finset.univ_nonempty
      (fun j => Real.exp (scores j) / old_denom)) := by
  intro old_denom new_denom
  -- The sup' of smaller values is strictly less than the sup' of larger values
  -- Use sup'_lt_iff: sup' f < sup' g ↔ ∀ i, f i < sup' g
  rw [Finset.sup'_lt_iff]
  intro j _
  -- For each j: exp(scores j) / new_denom < sup' (exp(scores ·) / old_denom)
  calc Real.exp (scores j) / new_denom
      < Real.exp (scores j) / old_denom := fan_effect scores s_new j
    _ ≤ Finset.sup' Finset.univ Finset.univ_nonempty
          (fun j => Real.exp (scores j) / old_denom) :=
        Finset.le_sup' (fun j => Real.exp (scores j) / old_denom) (Finset.mem_univ j)
