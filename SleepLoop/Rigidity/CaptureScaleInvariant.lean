/-
  SleepLoop/Rigidity/CaptureScaleInvariant.lean

  Corollary (cor:capture_scale_invariant): Scale invariance of the capture decision.
  For any beta > 0, the capture decision under query q' = beta*q is identical
  to that under q: q'^T E(tau) > max_{k in M} q'^T m_k iff q^T E(tau) > max_{k in M} q^T m_k.
  Level: A.
-/
import SleepLoop.Defs.Capture

open Finset

/-! ## Capture Scale Invariance -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- Scale invariance of the capture decision.
    For beta > 0, scaling the query q -> beta*q does not change which elements
    exceed the capture threshold: q . E(tau) > max_{k in M} q . m_k iff
    (beta*q) . E(tau) > max_{k in M} (beta*q) . m_k.
    Paper: cor:capture_scale_invariant. -/
theorem capture_scale_invariant
    (q : EuclideanSpace ℝ (Fin d))
    (M : Finset (EuclideanSpace ℝ (Fin d)))
    (hM : M.Nonempty)
    (e : EuclideanSpace ℝ (Fin d))
    (β : ℝ) (hβ : 0 < β) :
    edot (β • q) e > M.sup' hM (fun m => edot (β • q) m) ↔
    edot q e > M.sup' hM (fun m => edot q m) := by
  -- edot (β • q) v = β * edot q v by linearity of inner product
  have hlin : ∀ v, edot (β • q) v = β * edot q v := fun v =>
    real_inner_smul_left q v β
  simp only [hlin, gt_iff_lt, Finset.sup'_lt_iff, mul_lt_mul_iff_right₀ hβ]
