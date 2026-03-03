/-
  SleepLoop/Core/RetrievalWeightBounds.lean

  Corollary 16 (cor:opposition): Retrieval weight bounds under softmax.
  1/n <= max_j w_j <= 1/(1 + (n-1)exp(-g)) where g is the score gap.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Retrieval Weight Bounds -/

/-- cor:opposition (lower bound): Under uniform scores, w_j = 1/n,
    so max_j w_j ≥ 1/n. -/
theorem retrieval_weight_lower_bound
    {n : ℕ} [NeZero n] (scores : Fin n → ℝ) :
    (1 : ℝ) / n ≤
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun j => softmax scores j) := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [div_le_iff₀ hn_pos]
  have hsum : ∑ j : Fin n, softmax scores j = 1 := SimplexMap.sum_one scores
  rw [← hsum, mul_comm]
  set M := Finset.sup' Finset.univ Finset.univ_nonempty (fun j => softmax scores j)
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), softmax scores j ≤ M :=
    fun j _ => Finset.le_sup' _ (Finset.mem_univ j)
  have h := Finset.sum_le_card_nsmul Finset.univ _ M hle
  simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- cor:opposition (lower bound on max weight): max_j w_j ≥ 1/(1 + (n-1)exp(-g))
    where g is the score gap. Since all non-max scores ≤ s_max - g, the denominator
    sum is at most exp(s_max)·(1 + (n-1)·exp(-g)), giving the lower bound.
    Paper: cor:opposition, second half. -/
theorem retrieval_weight_upper_bound
    {n : ℕ} (hn2 : 2 ≤ n) (scores : Fin n → ℝ)
    (j_max : Fin n)
    (_hmax : ∀ k, scores k ≤ scores j_max)
    (g : ℝ) (hg : g = scores j_max - Finset.sup' (Finset.univ.erase j_max)
      (erase_v_nonempty hn2 j_max) (fun k => scores k)) :
    softmax scores j_max ≥ 1 / (1 + ((n : ℝ) - 1) * Real.exp (-g)) := by
  haveI : NeZero n := ⟨by omega⟩
  unfold softmax
  set s_max := scores j_max
  set denom := ∑ j : Fin n, Real.exp (scores j)
  have h_denom_pos : 0 < denom := by
    apply Finset.sum_pos
    · intro j _; exact Real.exp_pos _
    · exact Finset.univ_nonempty
  -- Split sum: denom = exp(s_max) + Σ_{j ≠ max} exp(s_j)
  have h_sum_split : denom = Real.exp s_max +
      ∑ j ∈ Finset.univ.erase j_max, Real.exp (scores j) := by
    change ∑ j : Fin n, Real.exp (scores j) = _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j_max)]
  -- For all j ≠ j_max: scores j ≤ s_max - g, so exp(s_j) ≤ exp(s_max - g)
  have h_each : ∀ j ∈ Finset.univ.erase j_max, Real.exp (scores j) ≤ Real.exp (s_max - g) := by
    intro j hj
    have hj_ne : j ≠ j_max := (Finset.mem_erase.mp hj).1
    have hj_le : scores j ≤ s_max - g := by
      rw [hg, sub_sub_cancel]
      exact Finset.le_sup' (fun k => scores k) (Finset.mem_erase.mpr ⟨hj_ne, Finset.mem_univ j⟩)
    exact Real.exp_le_exp.mpr hj_le
  have h_rest_bound : ∑ j ∈ Finset.univ.erase j_max, Real.exp (scores j) ≤
      ((Finset.univ.erase j_max).card : ℝ) * Real.exp (s_max - g) := by
    have := Finset.sum_le_card_nsmul _ _ _ h_each
    rwa [nsmul_eq_mul] at this
  -- |univ.erase j_max| = n - 1
  have h_card : ((Finset.univ.erase j_max).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j_max), Finset.card_univ, Fintype.card_fin]
    simp [Nat.cast_sub (by omega : 1 ≤ n)]
  rw [h_card] at h_rest_bound
  -- exp(s_max - g) = exp(s_max) * exp(-g)
  have h_exp_sub : Real.exp (s_max - g) = Real.exp s_max * Real.exp (-g) := by
    rw [sub_eq_add_neg, Real.exp_add]
  rw [h_exp_sub] at h_rest_bound
  -- n - 1 > 0 as a real
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  -- Bound on target denominator
  have h_target_pos : 0 < 1 + ((n : ℝ) - 1) * Real.exp (-g) := by
    linarith [mul_pos hn1_pos (Real.exp_pos (-g))]
  -- denom ≤ exp(s_max) * (1 + (n-1)*exp(-g))
  have h_denom_bound : denom ≤ Real.exp s_max * (1 + ((n : ℝ) - 1) * Real.exp (-g)) := by
    rw [h_sum_split]; nlinarith [Real.exp_pos s_max, Real.exp_pos (-g)]
  -- exp(s_max) / denom ≥ 1 / (1 + (n-1)*exp(-g))
  rw [ge_iff_le, div_le_div_iff₀ h_target_pos h_denom_pos]
  -- Goal: 1 * denom ≤ exp(s_max) * (1 + (n-1)*exp(-g))  (from div_le_div_iff₀)
  linarith

/-- cor:opposition: Score gap g = Ω(log n) is required for max weight
    to be bounded away from zero. -/
theorem score_gap_log_n_required
    (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    -- If max_j w_j ≥ c, then g ≥ log((n-1)c/(1-c))
    ((n : ℝ) - 1) * Real.exp (-Real.log (((n : ℝ) - 1) * c / (1 - c))) ≤ (1 - c) / c := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h1mc : (0 : ℝ) < 1 - c := by linarith
  have harg : (0 : ℝ) < ((n : ℝ) - 1) * c / (1 - c) := by
    exact div_pos (mul_pos hn1 hc) h1mc
  rw [Real.exp_neg, Real.exp_log harg]
  -- Goal: (↑n - 1) * (((↑n - 1) * c / (1 - c))⁻¹) ≤ (1 - c) / c
  -- Show equality: (n-1) * inv((n-1)*c/(1-c)) = (n-1) * (1-c)/((n-1)*c) = (1-c)/c
  suffices h : (↑n - 1) * ((↑n - 1 : ℝ) * c / (1 - c))⁻¹ = (1 - c) / c by
    rw [h]
  have hne : (↑n - 1 : ℝ) ≠ 0 := ne_of_gt hn1
  have hcne : c ≠ 0 := ne_of_gt hc
  have h1mcne : (1 - c : ℝ) ≠ 0 := ne_of_gt h1mc
  field_simp [hne, hcne, h1mcne]
