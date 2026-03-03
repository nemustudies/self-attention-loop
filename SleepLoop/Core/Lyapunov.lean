/-
  SleepLoop/Core/Lyapunov.lean

  Lemma 12 (lem:lyapunov): Lyapunov function for fixed-query consolidation.
  V(t+1) < V(t) whenever V(t) > 0, where V = max_{j != v} ||m_j - m_v||.
  Keystone result for convergence under repeated consolidation.
  Level: 𝒜₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.RetrievalGatedStability
import SleepLoop.Core.BlendRateBounds
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators

/-! ## Lyapunov Function for Fixed-Query Consolidation -/

variable {d n : ℕ}

/-- Auxiliary: The consolidation target T_j is strictly closer to
    the anchor v than V(t) (in squared norm), because the positive
    weight α_v^(j) contributes the zero vector m_v - m_v = 0. -/
theorem consolidation_target_closer_than_V
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v j : Fin n) (hjv : j ≠ v)
    (hn : 2 ≤ n)
    (hV_pos : 0 < lyapunovV M v hn) :
    ‖consolidationTarget φ q M j - M v‖ < lyapunovV M v hn := by
  -- Set up alpha = φ(scores)
  set scores : Fin n → ℝ := fun k => edot (M j + q) (M k) with scores_def
  set alpha := φ scores with alpha_def
  have halpha_pos : ∀ k, 0 < alpha k := fun k => PositiveSimplexMap.pos scores k
  have halpha_nonneg : ∀ k, 0 ≤ alpha k := fun k => le_of_lt (halpha_pos k)
  have halpha_sum : ∑ k : Fin n, alpha k = 1 := SimplexMap.sum_one scores
  -- Unfold consolidationTarget
  have hT : consolidationTarget φ q M j = ∑ k : Fin n, alpha k • M k := by
    unfold consolidationTarget; rfl
  -- Rewrite T_j - M v as ∑ α_k • (M k - M v)
  have hdiff : consolidationTarget φ q M j - M v =
      ∑ k : Fin n, alpha k • (M k - M v) := by
    have : ∑ k : Fin n, alpha k • (M k - M v) =
        (∑ k : Fin n, alpha k • M k) - (∑ k : Fin n, alpha k) • M v := by
      simp_rw [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
    rw [this, halpha_sum, one_smul, hT]
  -- Triangle inequality: ‖∑ α_k • (M k - M v)‖ ≤ ∑ α_k * ‖M k - M v‖
  have htri : ‖consolidationTarget φ q M j - M v‖ ≤
      ∑ k : Fin n, alpha k * ‖M k - M v‖ := by
    rw [hdiff]
    calc ‖∑ k : Fin n, alpha k • (M k - M v)‖
        ≤ ∑ k : Fin n, ‖alpha k • (M k - M v)‖ := norm_sum_le _ _
      _ = ∑ k : Fin n, alpha k * ‖M k - M v‖ := by
          congr 1; ext k
          rw [norm_smul_of_nonneg (halpha_nonneg k)]
  -- Each ‖M k - M v‖ ≤ V for k ≠ v, and ‖M v - M v‖ = 0
  set V := lyapunovV M v hn with V_def
  have hV_bound : ∀ k, k ≠ v → ‖M k - M v‖ ≤ V := by
    intro k hkv
    exact Finset.le_sup' (fun j => ‖M j - M v‖)
      (Finset.mem_erase.mpr ⟨hkv, Finset.mem_univ k⟩)
  -- Bound: ∑ α_k * ‖M k - M v‖ ≤ ∑ α_k * V = V
  have hbound : ∑ k : Fin n, alpha k * ‖M k - M v‖ ≤
      ∑ k : Fin n, alpha k * V := by
    apply Finset.sum_le_sum; intro k _
    by_cases hkv : k = v
    · subst hkv; simp [sub_self, norm_zero, mul_nonneg (halpha_nonneg k) (le_of_lt hV_pos)]
    · exact mul_le_mul_of_nonneg_left (hV_bound k hkv) (halpha_nonneg k)
  have hsum_eq : ∑ k : Fin n, alpha k * V = V := by
    rw [← Finset.sum_mul, halpha_sum, one_mul]
  -- Now show strict inequality: ∑ α_k * ‖M k - M v‖ < V
  -- because α_v > 0 contributes α_v * 0 = 0, while the total would be V
  -- if every term were α_k * V
  have hstrict : ∑ k : Fin n, alpha k * ‖M k - M v‖ < V := by
    rw [← hsum_eq]
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hkv : k = v
      · subst hkv; simp [sub_self, norm_zero, mul_nonneg (halpha_nonneg k) (le_of_lt hV_pos)]
      · exact mul_le_mul_of_nonneg_left (hV_bound k hkv) (halpha_nonneg k)
    · exact ⟨v, Finset.mem_univ v, by
        simp only [sub_self, norm_zero, mul_zero]
        exact mul_pos (halpha_pos v) hV_pos⟩
  linarith

/-- lem:lyapunov: Under A+, for fixed query q with capture disabled,
    V(t+1) < V(t) whenever V(t) > 0.
    V = max_{j ≠ v} ‖m_j - m_v‖ where v = argmax_k w_k. -/
theorem lyapunov_strict_decrease
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n)
    (v : Fin n)
    (hv : ∀ k, w k ≤ w v)
    (hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k)
    (hV_pos : 0 < lyapunovV M v hn) :
    let M' := consolidationStep φ br w q M (by omega)
    lyapunovV M' v hn < lyapunovV M v hn := by
  -- Setup
  intro M'
  set V := lyapunovV M v hn with V_def
  -- Anchor is unchanged by consolidation
  have hM'v : M' v = M v :=
    anchor_unchanged_by_consolidation φ br w q M (by omega) v hv (hw_pos v)
  -- Suffices: every ‖M' k - M' v‖ < V for k ≠ v
  -- lyapunovV M' v hn = sup' (univ.erase v) _ (fun j => ‖M' j - M' v‖)
  -- Use sup'_lt_iff to reduce to pointwise bound
  rw [show lyapunovV M' v hn =
    Finset.sup' (Finset.univ.erase v) (erase_v_nonempty hn v)
      (fun j => ‖M' j - M' v‖) from rfl]
  rw [Finset.sup'_lt_iff]
  intro k hk_mem
  have hkv : k ≠ v := (Finset.mem_erase.mp hk_mem).1
  -- Rewrite M' v = M v
  rw [hM'v]
  -- Get blend rate for k
  set rate_k := consolidationBlendRates br w (by omega : 0 < n) k with rate_k_def
  -- rate_k properties
  have hrate_range : 0 ≤ rate_k ∧ rate_k ≤ 1 :=
    blend_rate_range br w (by omega) (fun k => le_of_lt (hw_pos k))
      ⟨v, hw_pos v⟩ k
  have hrate_pos : 0 < rate_k :=
    blend_rate_nonanchor_pos φ br w (by omega) v k hkv hv hv_unique hw_pos
  have hrate_nonneg : 0 ≤ rate_k := hrate_range.1
  have hrate_le_one : rate_k ≤ 1 := hrate_range.2
  have hone_sub_nonneg : 0 ≤ 1 - rate_k := by linarith
  -- Note: we do not need 0 < 1 - rate_k; the strict bound comes from rate_k > 0
  -- and T_k being strictly closer than V
  -- Expand M' k
  have hM'k : M' k = (1 - rate_k) • M k + rate_k • consolidationTarget φ q M k := by
    rfl
  -- T_k is strictly closer to M v than V
  have hT_bound : ‖consolidationTarget φ q M k - M v‖ < V :=
    consolidation_target_closer_than_V φ q M v k hkv hn hV_pos
  -- ‖M k - M v‖ ≤ V
  have hMk_bound : ‖M k - M v‖ ≤ V :=
    Finset.le_sup' (fun j => ‖M j - M v‖)
      (Finset.mem_erase.mpr ⟨hkv, Finset.mem_univ k⟩)
  -- M' k - M v = (1 - rate_k) • (M k - M v) + rate_k • (T_k - M v)
  set T_k := consolidationTarget φ q M k with T_k_def
  have hdiff : M' k - M v =
      (1 - rate_k) • (M k - M v) + rate_k • (T_k - M v) := by
    rw [hM'k]
    -- Goal: (1-r) • M k + r • T_k - M v = (1-r) • (M k - M v) + r • (T_k - M v)
    simp only [smul_sub]
    -- (1-r)•Mk + r•Tk - Mv = (1-r)•Mk - (1-r)•Mv + (r•Tk - r•Mv)
    -- Rewrite Mv = ((1-r) + r) • Mv = (1-r)•Mv + r•Mv
    have hMv_split : M v = (1 - rate_k) • M v + rate_k • M v := by
      rw [← add_smul, sub_add_cancel, one_smul]
    conv_lhs => rw [hMv_split]
    -- Now goal should be closeable by ring_nf/module
    module
  -- Triangle inequality
  have htri : ‖M' k - M v‖ ≤
      (1 - rate_k) * ‖M k - M v‖ + rate_k * ‖consolidationTarget φ q M k - M v‖ := by
    rw [hdiff]
    calc ‖(1 - rate_k) • (M k - M v) + rate_k • (consolidationTarget φ q M k - M v)‖
        ≤ ‖(1 - rate_k) • (M k - M v)‖ + ‖rate_k • (consolidationTarget φ q M k - M v)‖ :=
          norm_add_le _ _
      _ = (1 - rate_k) * ‖M k - M v‖ + rate_k * ‖consolidationTarget φ q M k - M v‖ := by
          rw [norm_smul_of_nonneg hone_sub_nonneg, norm_smul_of_nonneg hrate_nonneg]
  -- Combine: (1-r)*V + r*‖T-v‖ < (1-r)*V + r*V = V
  calc ‖M' k - M v‖
      ≤ (1 - rate_k) * ‖M k - M v‖ + rate_k * ‖consolidationTarget φ q M k - M v‖ := htri
    _ < (1 - rate_k) * V + rate_k * V := by
        apply add_lt_add_of_le_of_lt
        · exact mul_le_mul_of_nonneg_left hMk_bound hone_sub_nonneg
        · exact mul_lt_mul_of_pos_left hT_bound hrate_pos
    _ = V := by ring
