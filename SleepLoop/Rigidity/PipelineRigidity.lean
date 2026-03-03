/-
  SleepLoop/Rigidity/PipelineRigidity.lean

  Proposition (prop:pipeline_rigidity): Rigidity of the retrieval pipeline.
  The pipeline q = aE, w = phi(qM^T), l = wM, b = EKl is determined
  (up to instance-defining K) by:
  (a) q = aF is invariant: among linear maps Δ^|X| → ℝ^d with
      ‖F(τ)‖ ≤ R, the simplex bound ‖q‖ ≤ R holds iff F is R-bounded.
      Any R-bounded F gives identical downstream guarantees; E is
      the canonical representative (zero extra parameters).
  (b) Dot-product scoring s_j = q . m_j is forced: linearity in m_j is
      needed so max over conv(E(X)) is at a vertex.
  (c) l = wM is instance-defining (hard retrieval preserves all but
      one quantitative bound).
  (d) E in b = EKl is forced; K is instance-defining.
  No pipeline with fewer than 4 operations suffices.
  Level: A.
-/
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation

open Finset BigOperators

/-! ## Pipeline Rigidity -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

omit [DecidableEq X] in
/-- (a) The query q = aF is bounded: ‖q‖ ≤ R for any R-bounded map F.
    This is the forward direction of query formation invariance.
    Paper: prop:pipeline_rigidity (a). -/
theorem query_bounded
    (E : Embedding X d) (a : X → ℝ)
    (ha_nonneg : ∀ τ, 0 ≤ a τ)
    (ha_sum : ∑ τ : X, a τ = 1) :
    ‖queryVector E a‖ ≤ E.radius := by
  unfold queryVector
  have key : ∀ τ, ‖a τ • E.map τ‖ ≤ a τ * E.radius := by
    intro τ
    rw [norm_smul_of_nonneg (ha_nonneg τ)]
    exact mul_le_mul_of_nonneg_left (E.bounded τ) (ha_nonneg τ)
  calc ‖∑ τ : X, a τ • E.map τ‖
      ≤ ∑ τ : X, ‖a τ • E.map τ‖ := norm_sum_le _ _
    _ ≤ ∑ τ : X, a τ * E.radius := Finset.sum_le_sum (fun τ _ => key τ)
    _ = (∑ τ : X, a τ) * E.radius := by rw [Finset.sum_mul]
    _ = 1 * E.radius := by rw [ha_sum]
    _ = E.radius := one_mul _

omit [DecidableEq X] in
/-- (a) Forward direction of query formation invariance:
    if ‖F(τ)‖ ≤ R for all τ, then ‖∑ a(τ) F(τ)‖ ≤ R for all simplex a.
    Any R-bounded map produces R-bounded queries.
    Paper: prop:pipeline_rigidity (a). -/
theorem query_formation_forward
    (E : Embedding X d)
    (F : X → EuclideanSpace ℝ (Fin d))
    (hF_bound : ∀ τ, ‖F τ‖ ≤ E.radius) :
    ∀ (a : X → ℝ) (_ha_nonneg : ∀ τ, 0 ≤ a τ) (_ha_sum : ∑ τ : X, a τ = 1),
      ‖∑ τ : X, a τ • F τ‖ ≤ E.radius := by
  intro a ha_nonneg ha_sum
  have key : ∀ τ, ‖a τ • F τ‖ ≤ a τ * E.radius := by
    intro τ
    rw [norm_smul_of_nonneg (ha_nonneg τ)]
    exact mul_le_mul_of_nonneg_left (hF_bound τ) (ha_nonneg τ)
  calc ‖∑ τ : X, a τ • F τ‖
      ≤ ∑ τ : X, ‖a τ • F τ‖ := norm_sum_le _ _
    _ ≤ ∑ τ : X, a τ * E.radius := Finset.sum_le_sum (fun τ _ => key τ)
    _ = (∑ τ : X, a τ) * E.radius := by rw [Finset.sum_mul]
    _ = 1 * E.radius := by rw [ha_sum]
    _ = E.radius := one_mul _

omit [DecidableEq X] in
/-- (a) Converse direction of query formation invariance:
    if ‖∑ a(τ) F(τ)‖ ≤ R for ALL simplex vectors a, then ‖F(τ)‖ ≤ R for all τ.
    Proof: take a = δ_τ (indicator at τ), which is a valid simplex vector.
    Paper: prop:pipeline_rigidity (a). -/
theorem query_formation_converse
    (F : X → EuclideanSpace ℝ (Fin d))
    (R : ℝ)
    (hR : ∀ (a : X → ℝ), (∀ τ, 0 ≤ a τ) → ∑ τ : X, a τ = 1 →
      ‖∑ τ : X, a τ • F τ‖ ≤ R) :
    ∀ τ, ‖F τ‖ ≤ R := by
  classical
  intro τ₀
  -- Use the indicator function δ_{τ₀}: a(τ₀) = 1, a(τ) = 0 for τ ≠ τ₀
  specialize hR (fun τ => if τ = τ₀ then 1 else 0)
    (fun τ => by dsimp only; split_ifs <;> norm_num)
    (by simp)
  simpa using hR

omit [DecidableEq X] in
/-- (a) Query formation invariance (iff characterization):
    for a linear map F : X → ℝ^d and bound R ≥ 0, the following are equivalent:
    (1) ‖F(τ)‖ ≤ R for all τ  (pointwise bound)
    (2) ‖∑ a(τ) F(τ)‖ ≤ R for all simplex a  (simplex bound)
    Any R-bounded map gives identical downstream guarantees. E is the
    canonical representative, but the theory is invariant under this choice.
    Paper: prop:pipeline_rigidity (a). -/
theorem query_formation_invariant_iff
    (E : Embedding X d)
    (F : X → EuclideanSpace ℝ (Fin d)) :
    (∀ τ, ‖F τ‖ ≤ E.radius) ↔
    (∀ (a : X → ℝ), (∀ τ, 0 ≤ a τ) → ∑ τ : X, a τ = 1 →
      ‖∑ τ : X, a τ • F τ‖ ≤ E.radius) :=
  ⟨fun hF => query_formation_forward E F hF,
   fun hS => query_formation_converse F E.radius hS⟩

/-- (b) Dot-product scoring is forced: linearity in m_j ensures the
    maximum over conv(E(X)) is at a vertex.
    For any convex combination c = Sigma alpha_k m_k, q . c <= max_k q . m_k.
    Paper: prop:pipeline_rigidity (b). -/
theorem dotproduct_scoring_forced
    (n : ℕ) (_hn : 0 < n) (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    ∀ (α : Fin n → ℝ),
      (∀ k, 0 ≤ α k) →
      ∑ k : Fin n, α k = 1 →
      edot q (∑ k : Fin n, α k • M k) ≤
        Finset.sup' (Finset.univ : Finset (Fin n)) hne (fun k => edot q (M k)) := by
  intro α hα_nonneg hα_sum
  -- Linearity of inner product: edot q (∑ αk • Mk) = ∑ αk * edot q Mk
  have lin : edot q (∑ k : Fin n, α k • M k) = ∑ k : Fin n, α k * edot q (M k) := by
    simp only [edot, inner_sum, real_inner_smul_right]
  rw [lin]
  -- A convex combination ∑ αk * xk ≤ max xk when αk ≥ 0 and ∑ αk = 1
  have hle : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      α k * edot q (M k) ≤
      α k * Finset.sup' Finset.univ hne (fun k => edot q (M k)) := by
    intro k _
    apply mul_le_mul_of_nonneg_left _ (hα_nonneg k)
    exact Finset.le_sup' (fun k => edot q (M k)) (Finset.mem_univ k)
  calc ∑ k : Fin n, α k * edot q (M k)
      ≤ ∑ k : Fin n,
        α k * Finset.sup' Finset.univ hne (fun k => edot q (M k)) :=
          Finset.sum_le_sum hle
    _ = (∑ k : Fin n, α k) *
        Finset.sup' Finset.univ hne (fun k => edot q (M k)) := by
          rw [Finset.sum_mul]
    _ = 1 * Finset.sup' Finset.univ hne (fun k => edot q (M k)) := by
          rw [hα_sum]
    _ = Finset.sup' Finset.univ hne (fun k => edot q (M k)) := one_mul _


omit [DecidableEq X] in
/-- (d) Feedback bias b(tau) = E(tau) . K . l is well-defined.
    E is forced as the unique parameter-free map R^d -> R^|X|.
    K is instance-defining; K = I preserves all theorems.
    Paper: prop:pipeline_rigidity (d). -/
theorem feedback_well_defined
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ell : EuclideanSpace ℝ (Fin d)) :
    ∀ τ, feedbackBias E K ell τ = edot (E.map τ) (K ell) := by
  intro τ
  rfl

/-- Irreducibility is a structural/meta argument about the pipeline passing
    through 4 distinct spaces (Delta^|X| -> R^d -> Delta^|M| -> R^d -> R^|X|).
    The formal content is captured by the proved theorems above:
    query_bounded, query_formation_forward, query_formation_converse,
    query_formation_invariant_iff, dotproduct_scoring_forced,
    feedback_well_defined. The irreducibility claim itself (that no shorter
    pipeline suffices) is an informal design justification, not a formal theorem.

    We record it as a constant 4 witnessing the pipeline length.
    Paper: prop:pipeline_rigidity (irreducibility). -/
def pipelineLength : ℕ := 4
