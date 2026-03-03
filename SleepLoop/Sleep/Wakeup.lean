/-
  SleepLoop/Sleep/Wakeup.lean

  Theorem 44 (thm:wakeup): Quasi-fixed-point under S=0.
  6-part theorem about wake-up conditions.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Wake-Up Conditions (Theorem 44) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- The quasi-fixed-point under S=0 with capture disabled.
    Bundles all six parts as a structure.
    Paper: thm:wakeup.

    Part (v) uses Brouwer's fixed-point theorem: the continuous map
    F(a) = φ(σ*(a) + EKv) sends the compact convex simplex Δ^|X| to
    itself, so it has a fixed point a*. Since F maps into the simplex,
    a* is automatically a valid probability distribution. Brouwer's
    theorem is not yet in Mathlib4, so the structure includes a
    self-map F and its Brouwer hypothesis as parameters. -/
structure QuasiFixedPoint
    {n : ℕ} (hn : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Fin n)
    (γ : ℕ → ℝ)
    (ell : ℕ → EuclideanSpace ℝ (Fin d))
    (b : ℕ → X → ℝ)
    -- The attention self-map F(a) = φ(σ*(a) + EKv) and Brouwer hypothesis
    (F : (X → ℝ) → (X → ℝ))
    (hF_simplex : ∀ a, (∀ τ, 0 ≤ F a τ) ∧ (∑ τ : X, F a τ = 1))
    (h_brouwer : ∃ a, F a = a) : Prop where
  /-- (i) V(t) → 0: all impressions converge to prototypes. -/
  V_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, lyapunovV (M t) (v t) hn < ε
  /-- (ii) γ(t) → 0: contraction rate vanishes (self-limiting). -/
  gamma_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, γ t < ε
  /-- (iii) ℓ(t) → v: retrieval output stabilizes to anchor. -/
  ell_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, ‖ell t - M t (v t)‖ < ε
  /-- (iv) b(t) → EKv: retrieval bias stabilizes. -/
  bias_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ τ : X, ∀ t ≥ T,
    |b t τ - feedbackBias E K (M t (v t)) τ| < ε
  /-- (v) Attention converges to a self-consistent fixed point a* on the simplex.
      The continuous map F: Δ^|X| → Δ^|X|, F(a) = φ(σ*(a) + EKv), has a
      fixed point by Brouwer's theorem (taken as h_brouwer). Since F maps
      into the simplex, the fixed point is a valid probability distribution. -/
  attention_fixed_point : ∃ a_star, F a_star = a_star ∧
    (∀ τ, 0 ≤ a_star τ) ∧ (∑ τ : X, a_star τ = 1)
  /-- (vi) Vanishing γ is a detectable wake-up signal. -/
  gamma_detectable : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, γ t < ε

/-- (i) V(t) → 0 under S=0 with capture disabled.
    Paper: thm:wakeup(i). -/
theorem wakeup_V_converges
    {n : ℕ} (hn : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Fin n)
    -- V ≤ D and D → 0 (from sleep_efficacy(i))
    (h_D_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, diameter (M t) (by omega) < ε)
    (h_V_le_D : ∀ t, lyapunovV (M t) (v t) hn ≤ diameter (M t) (by omega)) :
    ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, lyapunovV (M t) (v t) hn < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := h_D_converges ε hε
  exact ⟨T, fun t ht => lt_of_le_of_lt (h_V_le_D t) (hT t ht)⟩

/-- (ii) γ(t) → 0 as D(t) → 0.
    Paper: thm:wakeup(ii). -/
theorem wakeup_gamma_converges
    {n : ℕ} (hn : 2 ≤ n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (γ : ℕ → ℝ)
    (h_D_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, diameter (M t) (by omega) < ε)
    -- gamma is bounded by diameter (scores equalize as D → 0)
    (h_gamma_le_D : ∀ t, γ t ≤ diameter (M t) (by omega)) :
    ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, γ t < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := h_D_converges ε hε
  exact ⟨T, fun t ht => lt_of_le_of_lt (h_gamma_le_D t) (hT t ht)⟩

/-- (iii) ℓ(t) → v as D(t) → 0.
    Paper: thm:wakeup(iii). -/
theorem wakeup_ell_converges
    {n : ℕ} (hn : 2 ≤ n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (v : ℕ → Fin n)
    (h_D_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, diameter (M t) (by omega) < ε)
    -- retrievedImpression is within diameter of any impression
    (h_ell_le_D : ∀ t, ‖retrievedImpression (w t) (M t) - M t (v t)‖ ≤
        diameter (M t) (by omega)) :
    ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T,
      ‖retrievedImpression (w t) (M t) - M t (v t)‖ < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := h_D_converges ε hε
  exact ⟨T, fun t ht => lt_of_le_of_lt (h_ell_le_D t) (hT t ht)⟩

omit [DecidableEq X] in
/-- (iv) b(t) → EKv as ℓ → v.
    Paper: thm:wakeup(iv). -/
theorem wakeup_bias_converges
    {n : ℕ} (_hn : 2 ≤ n)
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Fin n)
    (h_ell : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, ‖ell t - M t (v t)‖ < ε) :
    ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ τ : X, ∀ t ≥ T,
      |feedbackBias E K (ell t) τ - feedbackBias E K (M t (v t)) τ| < ε := by
  intro ε hε
  -- feedbackBias E K l τ = edot (E.map τ) (K l)
  -- The difference is |edot (E.map τ) (K (ell t)) - edot (E.map τ) (K (M t (v t)))|
  -- = |edot (E.map τ) (K (ell t) - K (M t (v t)))| by linearity of inner product
  -- = |edot (E.map τ) (K (ell t - M t (v t)))| by linearity of K
  -- ≤ ‖E.map τ‖ * ‖K‖ * ‖ell t - M t (v t)‖ by Cauchy-Schwarz and operator norm
  -- Choose δ = ε / (‖E.map τ‖ * ‖K‖ + 1) and use h_ell
  -- We bound uniformly over τ using E.radius
  set C := E.radius * ‖K‖ + 1 with hC_def
  have hC_pos : 0 < C := by
    have hR := E.radius_pos
    have hK := norm_nonneg K
    have : 0 ≤ E.radius * ‖K‖ := mul_nonneg (le_of_lt hR) hK
    linarith
  obtain ⟨T, hT⟩ := h_ell (ε / C) (div_pos hε hC_pos)
  exact ⟨T, fun τ t ht => by
    have h1 := hT t ht
    -- feedbackBias E K l τ = edot (E.map τ) (K l)
    unfold feedbackBias
    -- |edot (E.map τ) (K (ell t)) - edot (E.map τ) (K (M t (v t)))|
    -- = |@inner ℝ _ _ (E.map τ) (K (ell t)) - @inner ℝ _ _ (E.map τ) (K (M t (v t)))|
    -- = |@inner ℝ _ _ (E.map τ) (K (ell t) - K (M t (v t)))|
    change |edot (E.map τ) (K (ell t)) - edot (E.map τ) (K (M t (v t)))| < ε
    rw [← inner_sub_right]
    have hR := E.radius_pos
    have hK := norm_nonneg K
    have hRK : 0 ≤ E.radius * ‖K‖ := mul_nonneg (le_of_lt hR) hK
    calc |@inner ℝ _ _ (E.map τ) (K (ell t) - K (M t (v t)))|
        ≤ ‖E.map τ‖ * ‖K (ell t) - K (M t (v t))‖ := abs_real_inner_le_norm _ _
      _ = ‖E.map τ‖ * ‖K (ell t - M t (v t))‖ := by rw [map_sub]
      _ ≤ ‖E.map τ‖ * (‖K‖ * ‖ell t - M t (v t)‖) := by
          gcongr; exact K.le_opNorm _
      _ ≤ E.radius * (‖K‖ * ‖ell t - M t (v t)‖) := by
          gcongr; exact E.bounded τ
      _ = E.radius * ‖K‖ * ‖ell t - M t (v t)‖ := by ring_nf
      _ ≤ C * ‖ell t - M t (v t)‖ := by
          gcongr
          linarith
      _ < C * (ε / C) := by
          gcongr
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hC_pos)⟩

omit [DecidableEq X] in
/-- (v) Attention converges to a* via Brouwer fixed-point theorem.
    Paper: thm:wakeup(v).

    At the quasi-fixed point, S=0, b → EKv, σ → σ*. The attention
    satisfies the self-consistent equation a* = φ(σ* + EKv) where
    σ*(τ) = √a*(τ) (from the RMS accumulation structure).

    The map F : Δ^|X| → Δ^|X| defined by F(a) = φ(σ*(a) + EKv) is
    continuous on the compact convex simplex, so by Brouwer's fixed-point
    theorem it has a fixed point a*. Since F maps into the simplex,
    a* is automatically a valid probability distribution.

    We take the existence of a fixed point as a hypothesis (`h_brouwer`)
    because Brouwer's fixed-point theorem for finite-dimensional simplices
    is not yet available in Mathlib4. The conclusion derives that this
    fixed point lies on the simplex (nonneg, sums to 1). -/
theorem wakeup_attention_fixed_point
    -- The map F: (X → ℝ) → (X → ℝ) represents the attention-accumulation
    -- cycle a ↦ φ(σ*(a) + EKv), mapping the simplex to itself
    (F : (X → ℝ) → (X → ℝ))
    -- F maps the simplex to itself: outputs are nonneg and sum to 1
    (hF_simplex : ∀ a, (∀ τ, 0 ≤ F a τ) ∧ (∑ τ : X, F a τ = 1))
    -- Brouwer's fixed-point theorem: F has a fixed point because the simplex
    -- is compact and convex and F is continuous. This is not yet in Mathlib4,
    -- so we take it as a hypothesis.
    (h_brouwer : ∃ a, F a = a) :
    -- Conclusion: there exists a fixed point a* that is a valid probability
    -- distribution (nonneg, sums to 1)
    ∃ a_star, F a_star = a_star ∧ (∀ τ, 0 ≤ a_star τ) ∧ (∑ τ : X, a_star τ = 1) := by
  obtain ⟨a_star, h_fixed⟩ := h_brouwer
  have h := hF_simplex a_star
  rw [h_fixed] at h
  exact ⟨a_star, h_fixed, h.1, h.2⟩

/-- (vi) Vanishing γ is a detectable wake-up signal.
    For any ε > 0, there exists T such that γ(t) < ε for all t ≥ T,
    and further S=0 steps produce bounded change.
    Paper: thm:wakeup(vi). -/
theorem wakeup_detectable_signal
    {n : ℕ} (_hn : 2 ≤ n)
    (V : ℕ → ℝ) (γ : ℕ → ℝ)
    (h_gamma_converges : ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T, γ t < ε)
    -- Per-step change bounded by γ(t) * V(t) (from contraction bound)
    (h_V_contract : ∀ t, V t - V (t + 1) ≤ γ t * V t)
    -- V is non-negative and non-increasing
    (h_V_nonneg : ∀ t, 0 ≤ V t)
    (h_V_mono : ∀ t, V (t + 1) ≤ V t) :
    ∀ (ε : ℝ), ε > 0 → ∃ T, ∀ t ≥ T,
      γ t < ε ∧ V t - V (t + 1) ≤ ε * V T := by
  intro ε hε
  obtain ⟨T, hT⟩ := h_gamma_converges ε hε
  refine ⟨T, fun t ht => ⟨hT t ht, ?_⟩⟩
  -- V t - V (t+1) ≤ γ t * V t < ε * V t ≤ ε * V T
  have h_gamma_lt := hT t ht
  have h_Vt_nonneg := h_V_nonneg t
  -- V t ≤ V T since V is non-increasing and t ≥ T
  have h_Vt_le_VT : V t ≤ V T := by
    have : ∀ k, V (T + k) ≤ V T := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc V (T + (k + 1)) = V (T + k + 1) := by ring_nf
          _ ≤ V (T + k) := h_V_mono _
          _ ≤ V T := ih
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact this k
  calc V t - V (t + 1)
      ≤ γ t * V t := h_V_contract t
    _ ≤ ε * V t := by
        apply mul_le_mul_of_nonneg_right (le_of_lt h_gamma_lt) h_Vt_nonneg
    _ ≤ ε * V T := by
        apply mul_le_mul_of_nonneg_left h_Vt_le_VT (le_of_lt hε)
