/-
  SleepLoop/Core/BoundedBias.lean

  Corollary 7 (cor:bounded): Bounded retrieval bias.
  |b(tau)| <= R^2 ||K||_op for all tau and all t.
  Level: 𝒜.
-/
import SleepLoop.Defs.Retrieval
import SleepLoop.Core.ConvexHullInvariance
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators

/-! ## Bounded Retrieval Bias -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

omit [DecidableEq X] in
/-- cor:bounded: The feedback bias is bounded by R² ‖K‖_op.
    Since ℓ ∈ conv(M) ⊆ conv(E(X)), ‖ℓ‖ ≤ R.
    Then |b(τ)| = |E(τ)ᵀ(Kℓ)| ≤ ‖E(τ)‖ · ‖K‖_op · ‖ℓ‖ ≤ R² ‖K‖_op. -/
theorem feedback_bias_bounded
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ell : EuclideanSpace ℝ (Fin d))
    (h_ell_bound : ‖ell‖ ≤ E.radius)
    (τ : X) :
    |feedbackBias E K ell τ| ≤ E.radius ^ 2 * ‖K‖ := by
  unfold feedbackBias edot
  -- Step 1: Cauchy-Schwarz: |⟪E(τ), Kℓ⟫| ≤ ‖E(τ)‖ * ‖Kℓ‖
  have h1 : |@inner ℝ (EuclideanSpace ℝ (Fin d)) _ (E.map τ) (K ell)| ≤
      ‖E.map τ‖ * ‖K ell‖ := abs_real_inner_le_norm _ _
  -- Step 2: Operator norm bound: ‖Kℓ‖ ≤ ‖K‖ * ‖ℓ‖
  have h2 : ‖K ell‖ ≤ ‖K‖ * ‖ell‖ := K.le_opNorm ell
  -- Step 3: ‖E(τ)‖ ≤ R
  have h3 : ‖E.map τ‖ ≤ E.radius := E.bounded τ
  -- Step 4: ‖ℓ‖ ≤ R
  have h4 : ‖ell‖ ≤ E.radius := h_ell_bound
  -- Step 5: Chain the bounds
  -- |inner| ≤ ‖E(τ)‖ * ‖Kℓ‖ ≤ R * (‖K‖ * R) = R² * ‖K‖
  calc |@inner ℝ (EuclideanSpace ℝ (Fin d)) _ (E.map τ) (K ell)|
      ≤ ‖E.map τ‖ * ‖K ell‖ := h1
    _ ≤ ‖E.map τ‖ * (‖K‖ * ‖ell‖) := by
        apply mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ E.radius * (‖K‖ * E.radius) := by
        apply mul_le_mul h3 (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (le_of_lt E.radius_pos)
    _ = E.radius ^ 2 * ‖K‖ := by ring
