/-
  SleepLoop/Core/PrototypeFormation.lean

  Corollary 19 (cor:prototype): Prototype formation.
  Under fixed query + no capture, every row of M converges
  to the anchor v = argmax_k q . m_k.
  Level: 𝒜₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.Convergence

open Finset BigOperators

/-! ## Prototype Formation -/

variable {d n : ℕ}

/-- cor:prototype: Every row of M converges to the anchor v.
    Since V(t) = max_{j ≠ v} ‖m_j - m_v‖ → 0, we have m_j → m_v
    for all j. -/
theorem prototype_formation
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n)
    (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (hv : ∀ t k, w t k ≤ w t v)
    (hv_unique : ∀ t k, k ≠ v → w t k < w t v)
    (_h_step : ∀ t, M (t + 1) = consolidationStep φ br (w t) q (M t) (by omega))
    (_h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R)
    (h_V_conv : Filter.Tendsto (fun t => lyapunovV (M t) v hn)
      Filter.atTop (nhds 0))
    (j : Fin n) :
    Filter.Tendsto (fun t => ‖M t j - M t v‖) Filter.atTop (nhds 0) := by
  by_cases hjv : j = v
  · -- Case j = v: ‖m_v - m_v‖ = 0, constant zero sequence
    subst hjv
    simp only [sub_self, norm_zero]
    exact tendsto_const_nhds
  · -- Case j ≠ v: ‖m_j - m_v‖ ≤ V(t) and V(t) → 0
    -- Use squeeze theorem: 0 ≤ ‖m_j - m_v‖ ≤ V(t) → 0
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) h_V_conv
    -- ‖m_j(t) - m_v(t)‖ ≤ V(t) for all t
    unfold lyapunovV
    exact Finset.le_sup' (fun k => ‖M t k - M t v‖)
      (Finset.mem_erase.mpr ⟨hjv, Finset.mem_univ j⟩)
