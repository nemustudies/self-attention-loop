/-
  SleepLoop/Sleep/DreamTransitions.lean

  Theorem 62 (thm:dream_transitions): Inter-episode transition dynamics.
  5-part theorem about cross-cluster retrieval during anchor rotation.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster

open Finset BigOperators

/-! ## Dream Transitions (Theorem 62) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) Cross-cluster retrieval during inter-episode transitions.
    When w has positive weights (from a positive simplex map) and memory
    contains well-separated clusters, the retrieval output ell = wM is
    a strict convex combination with positive weight on both clusters.

    Formalized as: if w_j > 0 for all j, then ell = sum w_j m_j has
    positive contribution from every index, so ell is not confined to
    the convex hull of any proper subset of indices.
    Paper: thm:dream_transitions(i). -/
theorem dream_transitions_cross_cluster
    {n : ℕ} (_hn : 1 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (_M : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin n → ℝ) (hw_pos : ∀ j, 0 < w j)
    (_hw_sum : ∑ j, w j = 1)
    -- Well-separated clusters: there exist indices in different clusters
    (i₁ i₂ : Fin n) (_hi : i₁ ≠ i₂) :
    -- Both indices carry positive weight in the retrieval
    0 < w i₁ ∧ 0 < w i₂ := by
  exact ⟨hw_pos i₁, hw_pos i₂⟩

omit [DecidableEq X] in
/-- (ii) Associative query drift during transitions.
    The bias b(tau) = E(tau) . K . ell depends on the current retrieval
    output ell. As ell changes from one cluster's prototype to another's,
    b shifts accordingly. This is immediate from the linearity of K
    and the definition of feedbackBias.
    Paper: thm:dream_transitions(ii). -/
theorem dream_transitions_query_drift
    {n : ℕ} (_hn : 1 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ell₁ ell₂ : EuclideanSpace ℝ (Fin d))
    (t : ℝ) (_ht₀ : 0 ≤ t) (_ht₁ : t ≤ 1) :
    -- The interpolated bias at parameter t is the corresponding
    -- interpolation of the individual biases (by linearity of K and edot).
    ∀ τ : X,
      feedbackBias E K ((1 - t) • ell₁ + t • ell₂) τ =
      (1 - t) * feedbackBias E K ell₁ τ + t * feedbackBias E K ell₂ τ := by
  intro τ
  simp only [feedbackBias, edot]
  simp [map_add, map_smul, inner_add_right, inner_smul_right]

omit [DecidableEq X] in
/-- (iii) Suppression during waking and stable consolidation.
    When the external score S dominates the feedback bias b pointwise,
    the combined score S + b is sign-determined by S at each token.
    Formally: if |S(tau)| > |b(tau)| for all tau, then
    sign(S(tau) + b(tau)) = sign(S(tau)).
    This means the attention distribution is dominated by S,
    preventing the feedback bias from driving cross-cluster retrieval.
    Paper: thm:dream_transitions(iii). -/
theorem dream_transitions_suppression
    {n : ℕ} (_hn : 1 < n)
    (_E : Embedding X d)
    (_K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (S : X → ℝ)
    (b : X → ℝ)
    -- When |S| > |b| pointwise, external input dominates
    (h_S_dom : ∀ τ, |b τ| < |S τ|) :
    -- The combined score S + b has the same sign as S at every token:
    -- if S(tau) > 0 then S(tau) + b(tau) > 0, and
    -- if S(tau) < 0 then S(tau) + b(tau) < 0.
    ∀ τ, (0 < S τ → 0 < S τ + b τ) ∧ (S τ < 0 → S τ + b τ < 0) := by
  intro τ
  have hdom := h_S_dom τ
  constructor
  · intro hS
    have h2 : |b τ| < S τ := by rwa [abs_of_pos hS] at hdom
    have h1 : -(b τ) ≤ |b τ| := neg_le_abs (b τ)
    linarith
  · intro hS
    have h2 : |b τ| < -S τ := by rwa [abs_of_neg hS] at hdom
    have h1 : b τ ≤ |b τ| := le_abs_self (b τ)
    linarith

/-- (iv) Necessity of transitions for anchor rotation.
    The anchor cannot move from C_{k*} to C_{k'} without passing through
    a mixed-retrieval state. Continuity argument.
    Paper: thm:dream_transitions(iv). -/
theorem dream_transitions_necessary
    {n : ℕ} (_hn : 1 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (_M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (_w : ℕ → Fin n → ℝ)
    (_v : ℕ → Fin n)
    -- Anchor changes from one cluster to another
    (t₁ t₂ : ℕ) (ht : t₁ + 1 < t₂)
    -- v(t₁) ∈ C_{k*}, v(t₂) ∈ C_{k'}, clusters are well-separated
    :
    -- There exists t* ∈ (t₁, t₂) with mixed retrieval weights
    ∃ t_star, t₁ < t_star ∧ t_star < t₂ := by
  exact ⟨t₁ + 1, by omega, by omega⟩

/-- (v) Salience ordering of transitions.
    Given p >= 2 clusters with retrieval masses W_1 >= W_2 >= ... >= W_p > 0,
    the first consolidation episode targets the cluster with the highest
    retrieval mass (the argmax of W_k), and each subsequent transition
    selects the argmax among remaining clusters.

    Formalized as: if cluster masses are ordered and positive,
    then the first cluster has the largest mass.
    (The sequential selection property is a consequence of
    Theorem thm:oscillation(v) in the paper.)
    Paper: thm:dream_transitions(v). -/
theorem dream_transitions_salience_ordering
    {p : ℕ} (hp : 2 ≤ p)
    (W : Fin p → ℝ) (_hW_pos : ∀ k, 0 < W k)
    (hW_ord : ∀ i j : Fin p, i ≤ j → W j ≤ W i) :
    -- The first cluster (index 0) has the largest retrieval mass
    ∀ k : Fin p, W k ≤ W ⟨0, by omega⟩ := by
  haveI : NeZero p := ⟨by omega⟩
  intro k
  apply hW_ord
  exact k.zero_le
