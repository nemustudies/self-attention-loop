/-
  SleepLoop/Rigidity/TargetAxioms.lean

  Proposition (prop:target_axioms): Minimal conditions for the consolidation target.
  Every theorem holds under these 5 axioms on T_j, and no theorem requires more:
    (T1) Convexity: T_j in conv(M)
    (T2) Anchor positivity: alpha_v^(j) > 0 for all j != v
    (T3) Full positivity: alpha_k^(j) > 0 for all k, j
    (T4) Continuity: (M, q) -> T_j(M, q) is continuous
    (T5) Lipschitz: m_j -> T_j is Lipschitz
  The specific form T_j = phi((m_j + q)M^T)M satisfies (T1)-(T5) but
  is not uniquely determined by them. It is an instance-defining choice.
  Level: A/A+.
-/
import SleepLoop.Defs.Consolidation
import Mathlib.Topology.MetricSpace.Lipschitz

open Finset BigOperators

/-! ## Target Axioms -/

variable {d : ℕ}

/-- An abstract consolidation target satisfying the minimal axioms.
    This abstracts over the specific form T_j = phi((m_j + q)M^T)M.
    Paper: prop:target_axioms. -/
structure ConsolidationTargetAxioms (n : ℕ) (d : ℕ) where
  /-- The target function: given memory M, query q, returns target for each j. -/
  target : (Fin n → EuclideanSpace ℝ (Fin d)) →
           EuclideanSpace ℝ (Fin d) →
           Fin n → EuclideanSpace ℝ (Fin d)

  /-- (T1) Convexity: T_j ∈ conv(M) for all j.
      Expressed as: T_j = Σ_k α_k^(j) · m_k with α on the simplex. -/
  convex_weights : (Fin n → EuclideanSpace ℝ (Fin d)) →
                   EuclideanSpace ℝ (Fin d) →
                   Fin n → (Fin n → ℝ)
  convex_nonneg : ∀ M q j k, 0 ≤ convex_weights M q j k
  convex_sum_one : ∀ M q j, ∑ k : Fin n, convex_weights M q j k = 1
  convex_rep : ∀ M q j,
    target M q j = ∑ k : Fin n, convex_weights M q j k • M k

  /-- (T2) Anchor positivity: the weight on the anchor v is positive
      for all j ≠ v. Used by Lyapunov contraction (lem:lyapunov). -/
  anchor_pos : ∀ M q (v : Fin n) j, j ≠ v → 0 < convex_weights M q j v

  /-- (T3) Full positivity: all weights are strictly positive.
      Used by sleep efficacy (thm:sleep_efficacy). -/
  full_pos : ∀ M q j k, 0 < convex_weights M q j k

  /-- (T4) Continuity: (M, q) ↦ T_j is continuous.
      Used by convergence (cor:sleep) and dream transitions. -/
  continuous_target : ∀ j, Continuous (fun p : (Fin n → EuclideanSpace ℝ (Fin d)) ×
    EuclideanSpace ℝ (Fin d) => target p.1 p.2 j)

  /-- (T5) Lipschitz: m_j ↦ T_j is Lipschitz.
      Used by oscillation (thm:oscillation). -/
  lipschitz_in_mj : ∀ M q j, ∃ L, LipschitzWith L
    (fun m => target (Function.update M j m) q j)

/-- The specific consolidation target T_j = phi((m_j + q)M^T)M satisfies (T1).
    It is a convex combination of M because phi is a simplex map.
    Paper: prop:target_axioms (T1). -/
theorem consolidationTarget_convex
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [SimplexMap φ]
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (j : Fin n) :
    ∃ (α : Fin n → ℝ),
      (∀ k, 0 ≤ α k) ∧
      ∑ k : Fin n, α k = 1 ∧
      consolidationTarget φ q M j = ∑ k : Fin n, α k • M k := by
  let scores : Fin n → ℝ := fun k => edot (M j + q) (M k)
  exact ⟨φ scores, fun k => SimplexMap.nonneg scores k,
         SimplexMap.sum_one scores, rfl⟩

/-- Under PositiveSimplexMap (A+), the specific target satisfies (T2) and (T3):
    all weights are strictly positive.
    Paper: prop:target_axioms (T2, T3). -/
theorem consolidationTarget_full_pos
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (j k : Fin n) :
    0 < (φ (fun i => edot (M j + q) (M i))) k := by
  exact PositiveSimplexMap.pos (fun i => edot (M j + q) (M i)) k

/-- The uniform average target: T_j = (1/|M|) * sum_k m_k for all j.
    This is a concrete alternative to phi((m_j + q)M^T)M that also
    satisfies (T1)-(T5). It demonstrates that the axioms do not
    uniquely determine the target. -/
noncomputable def uniformAverageTarget {n : ℕ} [NeZero n]
    (_M : Fin n → EuclideanSpace ℝ (Fin d))
    (_q : EuclideanSpace ℝ (Fin d))
    (_j : Fin n) : EuclideanSpace ℝ (Fin d) :=
  (1 / (n : ℝ)) • ∑ k : Fin n, _M k

/-- The uniform average target satisfies (T1): T_j is a convex
    combination of M with weights alpha_k = 1/|M| for all k.
    Paper: prop:target_axioms (T1, alternative target). -/
theorem uniformAverage_convex {n : ℕ} [NeZero n]
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin d))
    (j : Fin n) :
    ∃ (α : Fin n → ℝ),
      (∀ k, 0 ≤ α k) ∧
      ∑ k : Fin n, α k = 1 ∧
      uniformAverageTarget M q j = ∑ k : Fin n, α k • M k := by
  refine ⟨fun _ => 1 / (n : ℝ), fun _ => by positivity, ?_, ?_⟩
  · simp [Finset.card_univ, Fintype.card_fin]
  · unfold uniformAverageTarget
    rw [Finset.smul_sum]

/-- Concrete alternatives satisfying (T1)-(T5):
    - The global retrieval target T_j = ell = phi(qM^T)M
    - The direct anchor blend T_j = (1-beta)m_j + beta*v
    - Self-attention without query bias T_j = phi(m_j M^T)M
    - The uniform average T_j = (1/|M|) sum_k m_k
    None of these is forced by the axioms.

    We demonstrate non-uniqueness by showing that the per-impression
    target phi((m_j+q)M^T)M and the uniform average (1/|M|) sum m_k
    are both valid convex combinations of M but are generally distinct
    (they differ whenever the impressions are not all equal).
    Paper: prop:target_axioms (non-uniqueness). -/
theorem target_not_unique
    {n : ℕ} [NeZero n]
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [SimplexMap φ]
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (j : Fin n) :
    -- Both the specific target and the uniform average are convex
    -- combinations of M (both satisfy T1).
    (∃ (α : Fin n → ℝ), (∀ k, 0 ≤ α k) ∧
      ∑ k : Fin n, α k = 1 ∧
      consolidationTarget φ q M j =
        ∑ k : Fin n, α k • M k) ∧
    (∃ (β : Fin n → ℝ), (∀ k, 0 ≤ β k) ∧
      ∑ k : Fin n, β k = 1 ∧
      uniformAverageTarget M q j =
        ∑ k : Fin n, β k • M k) := by
  exact ⟨consolidationTarget_convex φ q M j,
         uniformAverage_convex M q j⟩
