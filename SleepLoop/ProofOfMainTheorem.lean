/-
  SleepLoop/ProofOfMainTheorem.lean

  Proves `mainTheorem : StatementOfTheorem` by connecting the Mathlib-only
  inline definitions in MainTheorem.lean to the project's existing theorems.
-/
import SleepLoop.MainTheorem
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.BlendRate
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.Convergence
import SleepLoop.Rigidity.AccumulationRigidity
import SleepLoop.CaptureInertness.SoftmaxLipschitz

open Finset BigOperators Filter

/-! ## Glue: connecting inline definitions to project definitions -/

/-- Convert AdmissibleBlendRate to project BlendRate. -/
private def toBlendRate (br : AdmissibleBlendRate) : BlendRate :=
  ⟨br.fn, br.maps_to, br.at_zero, br.at_one, br.pos_interior, br.continuous_fn⟩

/-- consolidationStep' with AdmissibleBlendRate = consolidationStep with BlendRate. -/
private theorem consolidationStep'_eq {d n : ℕ}
    (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (br : AdmissibleBlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hM : 0 < n) :
    consolidationStep' φ br w q M hM =
    consolidationStep φ (toBlendRate br) w q M hM := by
  simp only [consolidationStep', consolidationStep, consolidationBlendRates,
    consolidationTarget, toBlendRate]

/-! ## Part 1: Convergence -/

private theorem proof_convergence : Convergence := by
  intro d n hn psm br q v M w hv hv_unique hw_pos h_step h_bounded h_weight_gap
  -- Construct the project's PositiveSimplexMap instance
  haveI : PositiveSimplexMap psm.φ := {
    nonneg := psm.nonneg
    sum_one := psm.sum_one
    pos := psm.pos
    order_preserving := psm.order_preserving
    cont := psm.cont
  }
  let br' := toBlendRate br
  -- lyapunovV' and lyapunovV are definitionally equal after unfolding
  suffices h : Tendsto (fun t => lyapunovV (M t) v hn) atTop (nhds 0) by
    convert h using 1
  -- The step condition translates
  have h_step' : ∀ t, M (t + 1) = consolidationStep psm.φ br' (w t) q (M t) (by omega) := by
    intro t; rw [← consolidationStep'_eq]; exact h_step t
  exact convergence_under_consolidation psm.φ br' q hn v M w hv hv_unique hw_pos
    h_step' h_bounded h_weight_gap

/-! ## Part 2: Accumulation Rigidity -/

private theorem proof_accumulation_rigidity : AccumulationRigidity := by
  intro C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec hf_pos σ_lim hσ_pos hσ_conv
  exact accumulation_rigidity_aggregate C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec
    hf_pos σ_lim hσ_pos hσ_conv

/-! ## Part 3: Sublinear → σ → 0 -/

private theorem proof_sublinear_zero : SublinearZero := by
  intro C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec hf_pos hf_sub
  exact accum_sublinear_implies_sigma_zero C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec
    hf_pos hf_sub

/-! ## Part 4: Superlinear → σ → ∞ -/

private theorem proof_superlinear_unbounded : SuperlinearUnbounded := by
  intro C a f N₀ hN₀ δ hδ ha_lb hC_pos hC_rec hf_pos hf_superlinear
  exact accum_superlinear_implies_sigma_unbounded C a f N₀ hN₀ δ hδ ha_lb hC_pos hC_rec
    hf_pos hf_superlinear

/-! ## Part 5: Softmax Lipschitz -/

private theorem proof_softmax_lipschitz : SoftmaxLipschitz := by
  intro n _ x y
  -- Inline defs are definitionally equal to project defs
  change l1Norm' (fun i => softmax' x i - softmax' y i) ≤
    2 * linfNorm' (fun i => x i - y i)
  simp only [softmax', l1Norm', linfNorm']
  exact softmax_lipschitz x y

/-! ## Main Theorem -/

/-- The main theorem of the SleepLoop formalization. -/
theorem mainTheorem : StatementOfTheorem :=
  ⟨proof_convergence, proof_accumulation_rigidity, proof_sublinear_zero,
   proof_superlinear_unbounded, proof_softmax_lipschitz⟩
