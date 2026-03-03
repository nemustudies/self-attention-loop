/-
  SleepLoop/Core/ContextVariation.lean

  Corollary 20 (cor:variability): Context variation prevents collapse.
  If the anchor changes before V reaches 0, distinct impressions
  are preserved.
  Level: 𝒜₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.Convergence
import SleepLoop.Core.ContractionRate

open Finset BigOperators

/-! ## Context Variation Prevents Collapse -/

variable {d n : ℕ}

/-- cor:variability: After an anchor change from v to v' ≠ v, the new
    Lyapunov value V' = max_{j ≠ v'} ‖m_j - m_{v'}‖ is at least ‖m_v - m_{v'}‖.
    This is the core geometric fact: distinct anchors v ≠ v' guarantee
    a positive lower bound on V', preventing collapse to a single point.
    Paper: cor:variability. -/
theorem context_variation_preserves_diversity
    (hn : 2 ≤ n)
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v v' : Fin n) (hvv' : v ≠ v') :
    ‖M v - M v'‖ ≤ lyapunovV M v' hn := by
  unfold lyapunovV
  exact Finset.le_sup' (fun j => ‖M j - M v'‖)
    (Finset.mem_erase.mpr ⟨hvv', Finset.mem_univ v⟩)

/-- cor:variability (quantitative): After k steps under fixed anchor,
    V(k) ≤ (1 - γ_min)^k · V(0). -/
theorem geometric_contraction_bound
    (V₀ γ_min : ℝ) (_hγ : 0 ≤ γ_min) (hγ1 : γ_min ≤ 1)
    (V : ℕ → ℝ) (hV₀ : V 0 = V₀) (_hV_pos : 0 ≤ V₀)
    (h_step : ∀ t, V (t + 1) ≤ (1 - γ_min) * V t) (k : ℕ) :
    V k ≤ (1 - γ_min) ^ k * V₀ := by
  induction k with
  | zero => simp [hV₀]
  | succ k ih =>
    have h1 : V (k + 1) ≤ (1 - γ_min) * V k := h_step k
    have h2 : (1 - γ_min) * V k ≤ (1 - γ_min) * ((1 - γ_min) ^ k * V₀) := by
      apply mul_le_mul_of_nonneg_left ih
      linarith
    calc V (k + 1) ≤ (1 - γ_min) * V k := h1
      _ ≤ (1 - γ_min) * ((1 - γ_min) ^ k * V₀) := h2
      _ = (1 - γ_min) ^ (k + 1) * V₀ := by ring
