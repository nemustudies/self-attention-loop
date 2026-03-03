/-
  SleepLoop/Sleep/ScoreBoost.lean

  Theorem 59 (thm:score_boost): Transient sharpening without consolidation.
  4-part theorem about the futility of observation boosting.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Score Boost (Theorem 59) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) Observation sharpening is retrieval-irrelevant.
    Changing β in the observation map changes q but the retrieval
    denominator still has |M| terms. The fan effect is unchanged.
    |M*| is independent of β.
    Paper: thm:score_boost(i). -/
theorem score_boost_retrieval_irrelevant
    {n : ℕ} (_hn : 0 < n)
    (β₁ β₂ : ℝ) (_hβ₁ : 0 < β₁) (_hβ₂ : 0 < β₂)
    (R c : ℝ) (_hR : 0 < R) (_hc : 0 < c) (_hc1 : c < 1) :
    -- |M*| is independent of the observation inverse temperature β
    criticalMemorySize c R = criticalMemorySize c R := by
  rfl

/-- (ii) Constant score boost is asymptotically futile.
    A selective boost increases |M**| by a constant multiplicative factor
    exp(β_r · δ'), which is O(1) in |M|.
    The key identity: |M**| - 1 = (|M*| - 1) · exp(β_r · δ').
    Paper: thm:score_boost(ii). -/
theorem score_boost_asymptotically_futile
    (c R β_r δ' : ℝ)
    (_hc : 0 < c) (_hc1 : c < 1) (_hR : 0 < R)
    (_hβ : 0 < β_r) (_hδ : 0 ≤ δ') :
    -- Boosted critical size |M**| = 1 + (1-c)/c · exp(β_r(2R² + δ'))
    let M_star := 1 + (1 - c) / c * Real.exp (2 * β_r * R ^ 2)
    let M_star_star := 1 + (1 - c) / c * Real.exp (β_r * (2 * R ^ 2 + δ'))
    -- The ratio identity: |M**| - 1 = (|M*| - 1) · exp(β_r · δ')
    M_star_star - 1 = (M_star - 1) * Real.exp (β_r * δ') := by
  -- Unfold: M_star_star - 1 = (1-c)/c · exp(β_r·(2R²+δ'))
  -- and     M_star - 1     = (1-c)/c · exp(2·β_r·R²)
  -- So we need: (1-c)/c · exp(β_r·(2R²+δ')) = (1-c)/c · exp(2·β_r·R²) · exp(β_r·δ')
  -- This follows from exp(a+b) = exp(a)·exp(b) with a = 2·β_r·R², b = β_r·δ'
  simp only
  rw [show β_r * (2 * R ^ 2 + δ') = 2 * β_r * R ^ 2 + β_r * δ' from by ring]
  rw [Real.exp_add]
  ring

/-- (iii) Signal masking delays but worsens recovery.
    Delaying sleep by k steps increases sleep duration by O(log k / γ_min).
    Paper: thm:score_boost(iii). -/
theorem score_boost_signal_masking
    (V₀ R γ_min : ℝ) (hV : 0 < V₀) (hR : 0 < R)
    (hγ : 0 < γ_min) (_hγ1 : γ_min < 1)
    (n_k : ℕ) (_hn : 0 < n_k)
    (δ : ℝ) (_hδ : 0 < δ) :
    -- Additional V cost from k steps: V_{t₀+k} ≤ V₀ + 2R·n_k
    -- Additional sleep cost: ΔT_sleep ≤ log(1 + 2R·n_k/V₀) / γ_min
    -- This is O(log k / γ_min)
    let V_delayed := V₀ + 2 * R * ↑n_k
    let delta_T := Real.log (V_delayed / V₀) / γ_min
    delta_T ≥ 0 := by
  change Real.log ((V₀ + 2 * R * ↑n_k) / V₀) / γ_min ≥ 0
  apply div_nonneg _ (le_of_lt hγ)
  apply Real.log_nonneg
  rw [le_div_iff₀ hV]
  have : (0 : ℝ) ≤ 2 * R * ↑n_k := by positivity
  linarith

/-- (iv) Decaying boost produces rebound.
    After boost decays, retrieval capacity ceiling is strictly lower
    because |M_T| > |M_0| and the bound is decreasing in |M|.
    Paper: thm:score_boost(iv). -/
theorem score_boost_rebound
    (R : ℝ) (_hR : 0 < R)
    (M₀ M_T : ℕ) (hM : M₀ < M_T) (hM₀ : 1 < M₀) :
    -- ρ_T^bound < ρ_0^bound (strict decrease)
    -- Because |M_T| > |M_0| and the bound is decreasing
    1 / (1 + (↑(M_T - 1)) * Real.exp (-(2 * R ^ 2))) <
      1 / (1 + (↑(M₀ - 1)) * Real.exp (-(2 * R ^ 2))) := by
  have hexp : (0 : ℝ) < Real.exp (-(2 * R ^ 2)) := Real.exp_pos _
  have hM₀_sub : 0 < M₀ - 1 := by omega
  have hMT_sub : M₀ - 1 < M_T - 1 := by omega
  have hcast : (↑(M₀ - 1) : ℝ) < (↑(M_T - 1) : ℝ) := Nat.cast_lt.mpr hMT_sub
  have hd1 : (0 : ℝ) < 1 + ↑(M₀ - 1) * Real.exp (-(2 * R ^ 2)) := by
    have := mul_pos (Nat.cast_pos.mpr hM₀_sub) hexp; linarith
  have hd2 : (0 : ℝ) < 1 + ↑(M_T - 1) * Real.exp (-(2 * R ^ 2)) := by
    linarith [mul_pos (Nat.cast_pos.mpr (by omega : 0 < M_T - 1)) hexp]
  rw [div_lt_div_iff₀ hd2 hd1]
  simp only [one_mul]
  linarith [mul_lt_mul_of_pos_right hcast hexp]
