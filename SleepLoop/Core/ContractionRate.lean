/-
  SleepLoop/Core/ContractionRate.lean

  Corollary 14 (cor:contraction): State-dependent contraction rate.
  V(t+1) <= (1 - gamma(t)) V(t) where
  gamma(t) = min_{j != v} lambda_j (1 - sqrt(1 - alpha_v^(j))).
  Level: 𝒜₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.Lyapunov
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

/-! ## State-Dependent Contraction Rate -/

variable {d n : ℕ}

/-- cor:contraction (definition): The contraction rate
    γ(t) = min_{j ≠ v} λ_j (1 - √(1 - α_v^(j))). -/
noncomputable def contractionRate
    (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) : ℝ :=
  let rates : Fin n → ℝ := consolidationBlendRates br w (by omega)
  let alpha_v : Fin n → ℝ := fun j => φ (fun k => edot (M j + q) (M k)) v
  let hne : ((Finset.univ : Finset (Fin n)).erase v).Nonempty := erase_v_nonempty hn v
  Finset.inf' ((Finset.univ : Finset (Fin n)).erase v) hne
    (fun j => rates j * (1 - Real.sqrt (1 - alpha_v j)))

/-- cor:contraction: V(t+1) ≤ (1 - γ(t)) V(t).
    Requires hw_pos for blend rate bounds and anchor stability. -/
theorem contraction_rate_bound
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n)
    (v : Fin n)
    (hv : ∀ k, w k ≤ w v)
    (_hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k) :
    let M' := consolidationStep φ br w q M (by omega)
    let hn' : 2 ≤ n := by omega
    let γ := contractionRate φ br w q M v hn'
    lyapunovV M' v (by omega) ≤ (1 - γ) * lyapunovV M v (by omega) := by
  intro M' hn' γ
  set V := lyapunovV M v hn with V_def
  have hne : (Finset.univ.erase v : Finset (Fin n)).Nonempty :=
    erase_v_nonempty hn v
  have hM'v : M' v = M v :=
    anchor_unchanged_by_consolidation φ br w q M (by omega) v hv (hw_pos v)
  have hV_nn : 0 ≤ V :=
    le_trans (norm_nonneg _)
      (Finset.le_sup' (fun j => ‖M j - M v‖) hne.choose_spec)
  have hrate_range :
      ∀ j, 0 ≤ consolidationBlendRates br w (by omega : 0 < n) j ∧
        consolidationBlendRates br w (by omega : 0 < n) j ≤ 1 :=
    fun j => blend_rate_range br w (by omega)
      (fun k => le_of_lt (hw_pos k)) ⟨v, hw_pos v⟩ j
  -- Helper: for 0 ≤ u ≤ 1, we have u ≤ √u
  have le_sqrt_self :
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 → u ≤ Real.sqrt u := by
    intro u hu0 hu1
    rw [Real.le_sqrt hu0 hu0]
    calc u ^ 2 = u * u := sq u
      _ ≤ u * 1 := mul_le_mul_of_nonneg_left hu1 hu0
      _ = u := mul_one u
  have hMk_le_V :
      ∀ k, k ≠ v → ‖M k - M v‖ ≤ V :=
    fun k hkv => Finset.le_sup' (fun j => ‖M j - M v‖)
      (Finset.mem_erase.mpr ⟨hkv, Finset.mem_univ k⟩)
  -- Reduce to pointwise: suffices ‖M' k - M v‖ ≤ (1-γ)*V for k ≠ v
  rw [show lyapunovV M' v (by omega) =
    Finset.sup' (Finset.univ.erase v) hne
      (fun j => ‖M' j - M' v‖) from rfl]
  rw [Finset.sup'_le_iff]
  intro k hk_mem
  have hkv : k ≠ v := (Finset.mem_erase.mp hk_mem).1
  rw [hM'v]
  -- Blend rate for k
  set rk := consolidationBlendRates br w (by omega : 0 < n) k
  have hrk_nn : 0 ≤ rk := (hrate_range k).1
  have hrk_le1 : rk ≤ 1 := (hrate_range k).2
  have h1rk : 0 ≤ 1 - rk := by linarith
  -- Consolidation target T_k and attention weights alpha
  set T_k := consolidationTarget φ q M k
  set scores_k : Fin n → ℝ := fun i => edot (M k + q) (M i)
  set ak := φ scores_k
  have hak_nn : ∀ i, 0 ≤ ak i :=
    fun i => SimplexMap.nonneg scores_k i
  have hak_sum : ∑ i : Fin n, ak i = 1 :=
    SimplexMap.sum_one scores_k
  -- Step 1: decompose M'k - Mv as convex combination of differences
  have hdiff : M' k - M v =
      (1 - rk) • (M k - M v) + rk • (T_k - M v) := by
    change (1 - rk) • M k + rk • T_k - M v =
      (1 - rk) • (M k - M v) + rk • (T_k - M v)
    simp only [smul_sub]
    have : M v = (1 - rk) • M v + rk • M v := by
      rw [← add_smul, sub_add_cancel, one_smul]
    conv_lhs => rw [this]
    module
  -- Step 2: triangle inequality for the blend
  have htri : ‖M' k - M v‖ ≤
      (1 - rk) * ‖M k - M v‖ + rk * ‖T_k - M v‖ := by
    rw [hdiff]
    calc ‖(1 - rk) • (M k - M v) + rk • (T_k - M v)‖
        ≤ ‖(1 - rk) • (M k - M v)‖ +
          ‖rk • (T_k - M v)‖ := norm_add_le _ _
      _ = (1 - rk) * ‖M k - M v‖ +
          rk * ‖T_k - M v‖ := by
          rw [norm_smul_of_nonneg h1rk, norm_smul_of_nonneg hrk_nn]
  -- Step 3: bound ‖T_k - M v‖ ≤ (1 - ak v) * V
  have hTk_diff : T_k - M v =
      ∑ i : Fin n, ak i • (M i - M v) := by
    have : ∑ i : Fin n, ak i • (M i - M v) =
      (∑ i : Fin n, ak i • M i) -
      (∑ i : Fin n, ak i) • M v := by
      simp_rw [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
    rw [this, hak_sum, one_smul]; rfl
  have hTk_bound : ‖T_k - M v‖ ≤ (1 - ak v) * V := by
    -- Triangle: ‖∑ ak_i (Mi - Mv)‖ ≤ ∑ ak_i ‖Mi - Mv‖
    have tri : ‖T_k - M v‖ ≤
        ∑ i : Fin n, ak i * ‖M i - M v‖ := by
      rw [hTk_diff]
      calc ‖∑ i, ak i • (M i - M v)‖
          ≤ ∑ i, ‖ak i • (M i - M v)‖ := norm_sum_le _ _
        _ = ∑ i, ak i * ‖M i - M v‖ := by
            congr 1; ext i; rw [norm_smul_of_nonneg (hak_nn i)]
    -- Split sum at v: total = f(v) + rest
    have split : ∑ i : Fin n, ak i * ‖M i - M v‖ =
        ak v * ‖M v - M v‖ +
        ∑ i ∈ Finset.univ.erase v,
          ak i * ‖M i - M v‖ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    -- f(v) = 0
    have v_zero : ak v * ‖M v - M v‖ = 0 := by
      simp [sub_self, norm_zero, mul_zero]
    -- rest ≤ (1 - ak v) * V
    have rest_le : ∑ i ∈ Finset.univ.erase v,
        ak i * ‖M i - M v‖ ≤ (1 - ak v) * V := by
      calc ∑ i ∈ Finset.univ.erase v, ak i * ‖M i - M v‖
          ≤ ∑ i ∈ Finset.univ.erase v, ak i * V := by
            apply Finset.sum_le_sum; intro i hi
            exact mul_le_mul_of_nonneg_left
              (hMk_le_V i (Finset.ne_of_mem_erase hi)) (hak_nn i)
        _ = (∑ i ∈ Finset.univ.erase v, ak i) * V := by
            rw [Finset.sum_mul]
        _ = (1 - ak v) * V := by
            congr 1
            have := Finset.add_sum_erase Finset.univ ak
              (Finset.mem_univ v)
            linarith [hak_sum]
    linarith [tri, split, v_zero, rest_le]
  -- Step 4: relax (1 - ak v) to √(1 - ak v) using le_sqrt_self
  have hak_v_le1 : ak v ≤ 1 := SimplexMap.le_one scores_k v
  have hTk_sqrt : ‖T_k - M v‖ ≤
      Real.sqrt (1 - ak v) * V := by
    calc ‖T_k - M v‖ ≤ (1 - ak v) * V := hTk_bound
      _ ≤ Real.sqrt (1 - ak v) * V := by
          apply mul_le_mul_of_nonneg_right _ hV_nn
          exact le_sqrt_self _ (by linarith) (by linarith [hak_nn v])
  -- Step 5: combine into (1 - rk*(1-√(1-ak v))) * V
  have combined : ‖M' k - M v‖ ≤
      (1 - rk * (1 - Real.sqrt (1 - ak v))) * V := by
    calc ‖M' k - M v‖
        ≤ (1 - rk) * ‖M k - M v‖ +
          rk * ‖T_k - M v‖ := htri
      _ ≤ (1 - rk) * V +
          rk * (Real.sqrt (1 - ak v) * V) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hMk_le_V k hkv) h1rk
          · exact mul_le_mul_of_nonneg_left hTk_sqrt hrk_nn
      _ = (1 - rk * (1 - Real.sqrt (1 - ak v))) * V := by
          ring
  -- Step 6: γ ≤ rk * (1-√(1-ak v)), hence result
  have hgamma_le :
      γ ≤ rk * (1 - Real.sqrt (1 - ak v)) := by
    change contractionRate φ br w q M v hn ≤ _
    unfold contractionRate; simp only []
    exact Finset.inf'_le _ hk_mem
  calc ‖M' k - M v‖
      ≤ (1 - rk * (1 - Real.sqrt (1 - ak v))) * V := combined
    _ ≤ (1 - γ) * V := by
        apply mul_le_mul_of_nonneg_right _ hV_nn
        linarith

/-- cor:contraction: γ(t) > 0 when V(t) > 0. -/
theorem contraction_rate_pos
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n)
    (v : Fin n)
    (hv : ∀ k, w k ≤ w v)
    (hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k) :
    0 < contractionRate φ br w q M v (by omega) := by
  -- PAPER: γ(t) = min_{j ≠ v} λ_j(1 - √(1 - α_v^(j))) > 0 requires:
  -- (1) λ_j > 0 for all j ≠ v (follows from hv_unique and hw_pos)
  -- (2) 1 - √(1 - α_v^(j)) > 0, i.e., α_v^(j) > 0
  -- Condition (2) holds because φ is a positive simplex map and
  -- ∑_k α_k^(j) = 1, α_v^(j) = φ((M_j + q)M^T)_v > 0 (positive map)
  -- Therefore each term in the min is positive, so γ(t) > 0.
  --
  -- PAPER: γ(t) = min_{j ≠ v} λ_j(1 - √(1 - α_v^(j))) > 0 requires:
  -- (1) λ_j > 0 for all j ≠ v (follows from hv_unique and hw_pos)
  -- (2) 1 - √(1 - α_v^(j)) > 0, i.e., α_v^(j) > 0
  -- Therefore each product term is positive, and so is the minimum.
  --
  -- γ = inf' (univ.erase v) (fun j => rates j * (1 - √(1 - α_v j)))
  -- To show 0 < inf', show each term > 0
  unfold contractionRate
  simp only []
  -- Use: lt_inf'_iff: a < inf' s hs f ↔ ∀ x ∈ s, a < f x
  rw [Finset.lt_inf'_iff]
  intro j hj
  have hjv : j ≠ v := Finset.ne_of_mem_erase hj
  apply mul_pos
  · -- rates j > 0: blend rate is positive for j ≠ v
    exact blend_rate_nonanchor_pos φ br w (by omega) v j hjv hv hv_unique hw_pos
  · -- 1 - √(1 - α_v j) > 0
    set scores_j : Fin n → ℝ := fun k => edot (M j + q) (M k)
    have hα_pos : 0 < φ scores_j v := PositiveSimplexMap.pos scores_j v
    have hα_le_one : φ scores_j v ≤ 1 := SimplexMap.le_one scores_j v
    have h1 : 1 - φ scores_j v < 1 := by linarith
    have h2 : 0 ≤ 1 - φ scores_j v := by linarith
    have h3 : Real.sqrt (1 - φ scores_j v) < 1 := by
      calc Real.sqrt (1 - φ scores_j v) < Real.sqrt 1 := by
            apply Real.sqrt_lt_sqrt h2 h1
        _ = 1 := Real.sqrt_one
    linarith
