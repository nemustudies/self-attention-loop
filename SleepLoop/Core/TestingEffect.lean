/-
  SleepLoop/Core/TestingEffect.lean

  The Testing Effect: retrieval of the anchor impression v preserves v
  exactly (lambda_v = 0) and displaces all competitors (lambda_j > 0 for j != v).

  Wraps blend_rate_anchor_zero and blend_rate_nonanchor_pos from
  SleepLoop.Core.BlendRateBounds.

  Level: A_+.
-/
import SleepLoop.Core.BlendRateBounds

open Finset BigOperators

/-! ## Testing Effect -/

variable {d n : ℕ}

/-- The Testing Effect: retrieval of the anchor v preserves v exactly
    (lambda_v = 0) and displaces all competitors (lambda_j > 0 for j != v).

    Paper: Corollary (cor:testing). -/
theorem testing_effect
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (hn : 0 < n)
    (v : Fin n) (hv : ∀ k, w k ≤ w v)
    (hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k) :
    -- (i) Anchor is preserved: lambda_v = 0
    consolidationBlendRates br w hn v = 0 ∧
    -- (ii) All competitors are displaced: lambda_j > 0 for j != v
    (∀ j, j ≠ v → 0 < consolidationBlendRates br w hn j) :=
  ⟨blend_rate_anchor_zero br w hn v hv (hw_pos v),
   fun j hjv => blend_rate_nonanchor_pos φ br w hn v j hjv hv hv_unique hw_pos⟩
