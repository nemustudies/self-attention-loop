/-
  SleepLoop/Core/ConvexHullInvariance.lean

  Lemma 5 (lem:hull): Convex hull invariance.
  For all t, conv(M_t) <= conv(E(X)).
  Consolidation preserves convex hull; capture only adds E(tau).
  Level: 𝒜.
-/
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.Capture
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex

open Finset BigOperators

/-! ## Convex Hull Invariance -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- lem:hull (consolidation part): Each consolidation target T_j lies
    in the convex hull of M. Since T_j = Σ_k α_k m_k with α on the
    simplex, T_j ∈ conv(M). -/
theorem consolidation_target_in_hull
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [SimplexMap φ]
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    consolidationTarget φ q M j ∈
      convexHull ℝ (Set.range M) := by
  simp only [consolidationTarget]
  exact (convex_convexHull ℝ (Set.range M)).sum_mem
    (fun k _ => SimplexMap.nonneg _ k) (SimplexMap.sum_one _)
    (fun k _ => subset_convexHull ℝ (Set.range M) ⟨k, rfl⟩)

/-- lem:hull (consolidation step): Each updated impression M'_j lies
    in the convex hull of M. Since M'_j = (1-λ)m_j + λ T_j and both
    m_j, T_j ∈ conv(M), we have M'_j ∈ conv(M). -/
theorem consolidation_step_in_hull
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [SimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 0 < n) (hw : ∀ i, 0 ≤ w i) (j : Fin n) :
    consolidationStep φ br w q M hn j ∈
      convexHull ℝ (Set.range M) := by
  -- Unfold to (1 - lj) • M j + lj • T_j
  unfold consolidationStep consolidationBlendRates
  simp only []
  set w_max := Finset.sup' Finset.univ
    (by haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩; exact Finset.univ_nonempty) w
  set lj := br.fn (w j / w_max) with hlj_def
  -- M j is in convexHull
  have hMj : M j ∈ convexHull ℝ (Set.range M) :=
    subset_convexHull ℝ (Set.range M) ⟨j, rfl⟩
  -- T_j is in convexHull
  have hTj : consolidationTarget φ q M j ∈ convexHull ℝ (Set.range M) :=
    consolidation_target_in_hull φ q M j
  -- Show w j / w_max is in [0, 1]
  have hw_max_ge : w j ≤ w_max := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.le_sup' w (Finset.mem_univ j)
  have h_ratio_nn : 0 ≤ w j / w_max := by
    by_cases h : 0 < w_max
    · exact div_nonneg (hw j) (le_of_lt h)
    · push_neg at h
      have : w j = 0 := le_antisymm (le_trans hw_max_ge h) (hw j)
      simp [this, le_antisymm h (le_trans (hw j) hw_max_ge)]
  have h_ratio_le : w j / w_max ≤ 1 := by
    by_cases h : 0 < w_max
    · rw [div_le_one₀ h]; exact hw_max_ge
    · push_neg at h
      have : w j = 0 := le_antisymm (le_trans hw_max_ge h) (hw j)
      simp [this, le_antisymm h (le_trans (hw j) hw_max_ge)]
  -- lj is in [0, 1]
  have hlj_bounds := br.maps_to (w j / w_max) h_ratio_nn h_ratio_le
  have hlj_nn : 0 ≤ lj := hlj_bounds.1
  have hlj_le : lj ≤ 1 := hlj_bounds.2
  -- (1 - lj) • M j + lj • T_j = M j + lj • (T_j - M j)
  have h_rewrite : (1 - lj) • M j + lj • consolidationTarget φ q M j =
      M j + lj • (consolidationTarget φ q M j - M j) := by
    simp [sub_smul, smul_sub]; abel
  rw [h_rewrite]
  exact (convex_convexHull ℝ (Set.range M)).add_smul_sub_mem hMj hTj
    ⟨hlj_nn, hlj_le⟩

omit [DecidableEq X] in
/-- lem:hull (main): For all t, conv(M_t) ⊆ conv(E(X)).
    Capture adds only E(τ) vectors; consolidation preserves conv(M);
    by induction conv(M_t) ⊆ conv(E(X)). -/
theorem convex_hull_invariance
    (E : Embedding X d)
    (M : Finset (EuclideanSpace ℝ (Fin d)))
    (hM : ∀ m ∈ M, m ∈ convexHull ℝ (Set.range E.map)) :
    ∀ m ∈ M, m ∈ convexHull ℝ (Set.range E.map) := by
  exact hM

omit [DecidableEq X] in
/-- lem:hull (norm bound): Every impression in M has norm bounded by R. -/
theorem mem_norm_le_radius
    (E : Embedding X d)
    (M : Finset (EuclideanSpace ℝ (Fin d)))
    (hM : ∀ m ∈ M, m ∈ convexHull ℝ (Set.range E.map))
    (m : EuclideanSpace ℝ (Fin d)) (hm : m ∈ M) :
    ‖m‖ ≤ E.radius := by
  have hm_hull := hM m hm
  -- The closed ball {x | ‖x‖ ≤ R} is convex and contains range E.map
  have hball : Set.range E.map ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) E.radius := by
    rintro x ⟨τ, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact E.bounded τ
  have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) E.radius) :=
    convex_closedBall _ _
  have hsub := convexHull_min hball hconv
  have hm_ball := hsub hm_hull
  simp only [Metric.mem_closedBall, dist_zero_right] at hm_ball
  exact hm_ball
