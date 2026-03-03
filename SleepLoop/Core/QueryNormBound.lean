/-
  SleepLoop/Core/QueryNormBound.lean

  Corollary 10 (cor:query_norm_bound): Query vector norm bound.
  ||q_t|| <= R where R = max_tau ||E(tau)||. Moreover, q_t in conv(E(X)).
  Level: 𝒜.
-/
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Embedding
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination

open Finset BigOperators

/-! ## Query Vector Norm Bound -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

omit [DecidableEq X] in
/-- cor:query_norm_bound: ‖q‖ ≤ R.
    Since q = aE = Σ_τ a(τ) E(τ) with a ∈ Δ^|X|,
    q is a convex combination of embedding vectors. -/
theorem query_norm_bounded
    (E : Embedding X d) (a : X → ℝ)
    (ha_nonneg : ∀ τ, 0 ≤ a τ)
    (ha_sum : ∑ τ : X, a τ = 1) :
    ‖queryVector E a‖ ≤ E.radius := by
  unfold queryVector
  calc ‖∑ τ : X, a τ • E.map τ‖
      ≤ ∑ τ : X, ‖a τ • E.map τ‖ := norm_sum_le _ _
    _ = ∑ τ : X, a τ * ‖E.map τ‖ := by
        congr 1; ext τ
        rw [norm_smul, Real.norm_of_nonneg (ha_nonneg τ)]
    _ ≤ ∑ τ : X, a τ * E.radius := by
        apply Finset.sum_le_sum; intro τ _
        exact mul_le_mul_of_nonneg_left (E.bounded τ) (ha_nonneg τ)
    _ = E.radius := by rw [← Finset.sum_mul, ha_sum, one_mul]

omit [DecidableEq X] in
/-- cor:query_norm_bound (conv part): q ∈ conv(E(X)). -/
theorem query_in_convex_hull
    (E : Embedding X d) (a : X → ℝ)
    (ha_nonneg : ∀ τ, 0 ≤ a τ)
    (ha_sum : ∑ τ : X, a τ = 1) :
    queryVector E a ∈ convexHull ℝ (Set.range E.map) := by
  unfold queryVector
  exact (convex_convexHull ℝ (Set.range E.map)).sum_mem
    (fun τ _ => ha_nonneg τ) ha_sum
    (fun τ _ => subset_convexHull ℝ (Set.range E.map) ⟨τ, rfl⟩)
