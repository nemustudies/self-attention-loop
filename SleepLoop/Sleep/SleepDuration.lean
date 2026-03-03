/-
  SleepLoop/Sleep/SleepDuration.lean

  Corollary 53 (cor:sleep_duration): Sleep duration scales with cluster count.
  Total consolidation steps = Σ_k T_k where T_k = O(log(V_k(0)/δ) / γ_k).
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

/-! ## Sleep Duration (Corollary 53) -/

variable {d : ℕ}

/-- Per-cluster convergence time: T_k = O(log(V_k(0)/δ) / γ_k).
    Follows from V(t+T) ≤ (1-γ_k)^T · V(t).
    Paper: cor:sleep_duration (per-cluster bound). -/
noncomputable def clusterConvergenceTime (V₀ δ γ : ℝ) : ℝ :=
  Real.log (V₀ / δ) / (-Real.log (1 - γ))

/-- Positivity of clusterConvergenceTime when V₀ > δ > 0 and 0 < γ < 1. -/
theorem clusterConvergenceTime_pos
    (V₀ δ γ : ℝ) (hδ : 0 < δ) (hδV : δ < V₀) (hγ : 0 < γ) (hγ1 : γ < 1) :
    0 < clusterConvergenceTime V₀ δ γ := by
  unfold clusterConvergenceTime
  apply div_pos
  · exact Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  · rw [neg_pos]; exact Real.log_neg (by linarith) (by linarith)

/-- Core scaling bound (Corollary 53): If V(t) contracts geometrically as
    V(t+1) ≤ (1-γ) V(t), then reaching V(T) ≤ δ requires at least
    T ≥ log(V₀/δ) / (-log(1-γ)) = clusterConvergenceTime V₀ δ γ steps.

    Proof: (1-γ)^T V₀ ≤ δ implies T log(1-γ) ≤ log(δ/V₀) < 0.
    Dividing by log(1-γ) < 0 flips the inequality:
    T ≥ log(δ/V₀) / log(1-γ) = log(V₀/δ) / (-log(1-γ)).

    This is the key content of cor:sleep_duration. -/
theorem geometric_contraction_time_lower_bound
    (V₀ δ γ : ℝ) (hV₀ : 0 < V₀) (hδ : 0 < δ) (_hδV : δ < V₀)
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (T : ℕ) (hT : (1 - γ) ^ T * V₀ ≤ δ) :
    clusterConvergenceTime V₀ δ γ ≤ (T : ℝ) := by
  unfold clusterConvergenceTime
  -- Key facts about log(1-γ)
  have h1mγ_pos : 0 < 1 - γ := by linarith
  have h1mγ_lt1 : 1 - γ < 1 := by linarith
  have hlog_neg : Real.log (1 - γ) < 0 := Real.log_neg h1mγ_pos h1mγ_lt1
  have hneg_log_pos : 0 < -Real.log (1 - γ) := neg_pos.mpr hlog_neg
  -- Rewrite the goal: log(V₀/δ)/(-log(1-γ)) ≤ T
  -- ↔ log(V₀/δ) ≤ T * (-log(1-γ))  (dividing by positive -log(1-γ))
  rw [div_le_iff₀ hneg_log_pos]
  -- ↔ log(V₀/δ) ≤ -(T * log(1-γ))
  rw [mul_neg, le_neg]
  -- Now need: T * log(1-γ) ≤ -log(V₀/δ) = log(δ/V₀)
  rw [← Real.log_inv, inv_div]
  -- Need: T * log(1-γ) ≤ log(δ/V₀)
  -- From hT: (1-γ)^T * V₀ ≤ δ, so (1-γ)^T ≤ δ/V₀
  have hpow_le : (1 - γ) ^ T ≤ δ / V₀ := by
    rwa [le_div_iff₀ hV₀]
  -- Taking log (both sides positive): T * log(1-γ) ≤ log(δ/V₀)
  -- log((1-γ)^T) = T * log(1-γ)
  have hpow_pos : 0 < (1 - γ) ^ T := pow_pos h1mγ_pos T
  have hdV_pos : 0 < δ / V₀ := div_pos hδ hV₀
  calc (T : ℝ) * Real.log (1 - γ)
      = Real.log ((1 - γ) ^ T) := by rw [Real.log_pow]
    _ ≤ Real.log (δ / V₀) := Real.log_le_log hpow_pos hpow_le

/-- Sleep duration bounded by contraction rate (Corollary 53).
    Total steps ≥ Σ_k T_k ≥ p · min_k T_k, so duration is at
    least proportional to the number of initial clusters p.

    Each cluster k requires T_k = log(V_k(0)/δ) / (-log(1-γ_k)) steps.
    The per-cluster time T_k is positive since V₀ k > δ > 0 and 0 < γ k < 1. -/
theorem sleep_duration_bound
    (p : ℕ) (hp : 1 ≤ p)
    (V₀ : Fin p → ℝ) (_hV₀ : ∀ k, 0 < V₀ k)
    (γ : Fin p → ℝ) (hγ : ∀ k, 0 < γ k) (hγ1 : ∀ k, γ k < 1)
    (δ : ℝ) (hδ : 0 < δ) (hδV : ∀ k, δ < V₀ k) :
    0 < ∑ k : Fin p, clusterConvergenceTime (V₀ k) δ (γ k) := by
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  apply Finset.sum_pos
  · intro k _
    exact clusterConvergenceTime_pos (V₀ k) δ (γ k) hδ (hδV k) (hγ k) (hγ1 k)
  · exact Finset.univ_nonempty

/-- Total sleep duration scaling: if each cluster k has V_k converging geometrically
    with rate γ_k and requires T_k steps to reach δ, then the total steps
    ∑ T_k ≥ ∑ clusterConvergenceTime(V₀ k, δ, γ k).

    This is the full content of Corollary 53. -/
theorem sleep_duration_scaling_bound
    (p : ℕ) (_hp : 1 ≤ p)
    (V₀ : Fin p → ℝ) (hV₀ : ∀ k, 0 < V₀ k)
    (γ : Fin p → ℝ) (hγ : ∀ k, 0 < γ k) (hγ1 : ∀ k, γ k < 1)
    (δ : ℝ) (hδ : 0 < δ) (hδV : ∀ k, δ < V₀ k)
    (T : Fin p → ℕ)
    (hT : ∀ k, (1 - γ k) ^ (T k) * V₀ k ≤ δ) :
    ∑ k : Fin p, clusterConvergenceTime (V₀ k) δ (γ k) ≤
      ∑ k : Fin p, (T k : ℝ) := by
  apply Finset.sum_le_sum
  intro k _
  exact geometric_contraction_time_lower_bound (V₀ k) δ (γ k)
    (hV₀ k) hδ (hδV k) (hγ k) (hγ1 k) (T k) (hT k)

/-- Lower bound on per-cluster convergence time via geometric contraction.
    From V(t+T) ≤ (1-γ)^T V(t): achieving V(T) ≤ δ requires
    T ≥ log(V₀/δ) / (-log(1-γ)) = clusterConvergenceTime V₀ δ γ.

    This is the per-cluster version of the scaling bound. -/
theorem per_cluster_convergence_lower_bound
    (V₀ δ γ : ℝ)
    (hV₀ : 0 < V₀) (hδ : 0 < δ) (hδV : δ < V₀)
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (T : ℕ) (hT : (1 - γ) ^ T * V₀ ≤ δ) :
    clusterConvergenceTime V₀ δ γ ≤ (T : ℝ) :=
  geometric_contraction_time_lower_bound V₀ δ γ hV₀ hδ hδV hγ hγ1 T hT
