/-
  SleepLoop/Core/BlendRateBounds.lean

  Corollary 11 (cor:blend_rate_bounds): Blend rate bounds.
  Under A+ with |M| >= 2 and v = argmax_k w_k:
  lambda_v = 0 (anchor fixed), 0 < lambda_j <= 1 for j != v.
  Level: 𝒜₊.
-/
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.BlendRate
import SleepLoop.Defs.SimplexMap

open Finset BigOperators

/-! ## Blend Rate Bounds -/

variable {d n : ℕ}

/-- cor:blend_rate_bounds (anchor): λ_v = 0.
    Since v = argmax_k w_k, w_v/w_v = 1, and λ(1) = 0. -/
theorem blend_rate_anchor_zero
    (br : BlendRate) (w : Fin n → ℝ)
    (hn : 0 < n)
    (v : Fin n) (hv : ∀ k, w k ≤ w v) (hw_pos : 0 < w v) :
    consolidationBlendRates br w hn v = 0 := by
  unfold consolidationBlendRates
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h_sup_eq : Finset.sup' Finset.univ Finset.univ_nonempty w = w v := by
    apply le_antisymm
    · apply Finset.sup'_le; intro k _; exact hv k
    · exact Finset.le_sup' w (Finset.mem_univ v)
  rw [h_sup_eq, div_self (ne_of_gt hw_pos)]
  exact br.at_one

/-- cor:blend_rate_bounds (non-anchor positive): 0 < λ_j for j ≠ v.
    Since w_j < w_v (unique maximizer), w_j/w_v < 1,
    and λ is positive on [0,1). -/
theorem blend_rate_nonanchor_pos
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (hn : 0 < n)
    (v j : Fin n) (hjv : j ≠ v)
    (hv : ∀ k, w k ≤ w v)
    (hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k) :
    0 < consolidationBlendRates br w hn j := by
  unfold consolidationBlendRates
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h_sup_eq : Finset.sup' Finset.univ Finset.univ_nonempty w = w v := by
    apply le_antisymm
    · apply Finset.sup'_le; intro k _; exact hv k
    · exact Finset.le_sup' w (Finset.mem_univ v)
  rw [h_sup_eq]
  have hw_j_pos : 0 < w j := hw_pos j
  have hw_v_pos : 0 < w v := hw_pos v
  have h_ratio_nonneg : 0 ≤ w j / w v := div_nonneg (le_of_lt hw_j_pos) (le_of_lt hw_v_pos)
  have h_ratio_lt_one : w j / w v < 1 := (div_lt_one hw_v_pos).mpr (hv_unique j hjv)
  exact br.pos_interior (w j / w v) h_ratio_nonneg h_ratio_lt_one

/-- cor:blend_rate_bounds (range): 0 ≤ λ_j ≤ 1 for all j. -/
theorem blend_rate_range
    (br : BlendRate) (w : Fin n → ℝ)
    (hn : 0 < n)
    (hw_nonneg : ∀ k, 0 ≤ w k)
    (hw_max_pos : ∃ k, 0 < w k) (j : Fin n) :
    0 ≤ consolidationBlendRates br w hn j ∧
    consolidationBlendRates br w hn j ≤ 1 := by
  unfold consolidationBlendRates
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set w_max := Finset.sup' Finset.univ Finset.univ_nonempty w with hw_max_def
  obtain ⟨k, hk_pos⟩ := hw_max_pos
  have h_wmax_pos : 0 < w_max := lt_of_lt_of_le hk_pos (Finset.le_sup' w (Finset.mem_univ k))
  have h_ratio_nonneg : 0 ≤ w j / w_max :=
    div_nonneg (hw_nonneg j) (le_of_lt h_wmax_pos)
  have h_ratio_le_one : w j / w_max ≤ 1 :=
    div_le_one_of_le₀ (Finset.le_sup' w (Finset.mem_univ j)) (le_of_lt h_wmax_pos)
  exact br.maps_to (w j / w_max) h_ratio_nonneg h_ratio_le_one
