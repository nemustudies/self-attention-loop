/-
  SleepLoop/Core/RetrievalGatedStability.lean

  Lemma 3 (lem:stability): Retrieval-gated stability.
  Under A+, the anchor v = argmax_k w_k is unchanged by consolidation
  (lambda_v = 0), and the capture threshold in v's direction never decreases.
  Level: 𝒜₊.
-/
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Retrieval-Gated Stability -/

variable {d n : ℕ}

/-- lem:stability (part 1): The anchor v is unchanged by consolidation.
    Since λ_v = 0, the consolidation step preserves m_v exactly. -/
theorem anchor_unchanged_by_consolidation
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 0 < n)
    (v : Fin n) (hv : ∀ k, w k ≤ w v)
    (hw_pos : 0 < w v) :
    consolidationStep φ br w q M hn v = M v := by
  -- The consolidation step is: (1 - λ_v) • M v + λ_v • T_v
  -- where λ_v = br.fn(w v / max_k w_k). Since v maximizes w, w v / w_max = 1,
  -- so λ_v = br.fn(1) = 0, giving (1-0) • M v + 0 • T_v = M v.
  unfold consolidationStep consolidationBlendRates
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp only []
  have h_sup_eq : Finset.sup' Finset.univ Finset.univ_nonempty w = w v := by
    apply le_antisymm
    · apply Finset.sup'_le; intro k _; exact hv k
    · exact Finset.le_sup' w (Finset.mem_univ v)
  have hwv_ne : w v ≠ 0 := ne_of_gt hw_pos
  simp only [h_sup_eq, div_self hwv_ne, br.at_one, sub_zero, one_smul, zero_smul, add_zero]

/-- lem:stability (part 2): The capture threshold in v's direction
    never decreases after consolidation.
    For any q' with v = argmax_k q'ᵀm_k,
    max_{k ∈ M'} q'ᵀm_k ≥ max_{k ∈ M} q'ᵀm_k. -/
theorem capture_threshold_nondecreasing
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q q' : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 0 < n)
    (v : Fin n) (hv : ∀ k, w k ≤ w v)
    (hw_pos : 0 < w v)
    (_hv_max : ∀ k, edot q' (M k) ≤ edot q' (M v)) :
    let M' := consolidationStep φ br w q M hn
    edot q' (M' v) ≥ edot q' (M v) := by
  -- M' v = M v by anchor_unchanged_by_consolidation, so the inequality is trivial
  change edot q' (consolidationStep φ br w q M hn v) ≥ edot q' (M v)
  have h_anchor : consolidationStep φ br w q M hn v = M v :=
    anchor_unchanged_by_consolidation φ br w q M hn v hv hw_pos
  rw [h_anchor]
