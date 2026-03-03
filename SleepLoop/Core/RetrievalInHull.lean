/-
  SleepLoop/Core/RetrievalInHull.lean

  Corollary 9 (cor:retrieval_in_hull): Retrieval output lies in convex hull.
  For any query q with M nonempty, the retrieval output ell = wM
  satisfies ell in conv(M) <= conv(E(X)).
  Level: 𝒜.
-/
import SleepLoop.Defs.Retrieval
import SleepLoop.Core.ConvexHullInvariance
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination

open Finset BigOperators

/-! ## Retrieval Output Lies in Convex Hull -/

variable {d : ℕ}

/-- cor:retrieval_in_hull: The retrieved impression ℓ = wM lies
    in conv(M), since w is a convex weight vector (on the simplex)
    and ℓ = Σ_j w_j m_j is a convex combination. -/
theorem retrieval_in_convex_hull
    {n : ℕ} (w : Fin n → ℝ) (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin n, w j = 1) :
    retrievedImpression w M ∈ convexHull ℝ (Set.range M) := by
  unfold retrievedImpression
  exact (convex_convexHull ℝ (Set.range M)).sum_mem
    (fun j _ => hw_nonneg j) hw_sum
    (fun j _ => subset_convexHull ℝ (Set.range M) ⟨j, rfl⟩)

/-- cor:retrieval_in_hull (norm bound): ‖ℓ‖ ≤ R when M ⊆ conv(E(X)). -/
theorem retrieval_norm_bounded
    {n : ℕ} (w : Fin n → ℝ) (M : Fin n → EuclideanSpace ℝ (Fin d))
    (R : ℝ)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin n, w j = 1)
    (hM_bound : ∀ j, ‖M j‖ ≤ R) :
    ‖retrievedImpression w M‖ ≤ R := by
  unfold retrievedImpression
  calc ‖∑ j : Fin n, w j • M j‖
      ≤ ∑ j : Fin n, ‖w j • M j‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, w j * ‖M j‖ := by
        congr 1; ext j
        rw [norm_smul, Real.norm_of_nonneg (hw_nonneg j)]
    _ ≤ ∑ j : Fin n, w j * R := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hM_bound j) (hw_nonneg j)
    _ = R := by rw [← Finset.sum_mul, hw_sum, one_mul]
