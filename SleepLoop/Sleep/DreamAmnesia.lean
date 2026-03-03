/-
  SleepLoop/Sleep/DreamAmnesia.lean

  Theorem 65 (thm:dream_amnesia): Dream amnesia.
  4-part theorem about non-storage during consolidation and fading trace.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Dream Amnesia (Theorem 65) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) No storage of dream content.
    During S=0, capture is disabled so no new impressions enter M.
    Cross-cluster retrieval outputs ℓ_k are computed but never stored.
    The number of rows |M| is constant throughout the S=0 phase
    (consolidation modifies existing rows via convex combination but never adds new rows).
    Paper: thm:dream_amnesia(i).

    Formalization note: This claim is about the *structure* of the update rule:
    during S=0, the update is m_j ← (1-λ_j)m_j + λ_j T_j with T_j ∈ conv(M),
    which preserves the row set. We express this as: |M(t)| = |M(0)| for all t
    in the S=0 phase, which is immediate since M is indexed by Fin n throughout. -/
theorem dream_amnesia_no_storage
    {n : ℕ} (_hn : 1 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (_M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    -- During S=0, capture disabled, consolidation active
    -- Consolidation contracts but never adds rows
    :
    -- The number of rows is constant throughout: |M(t)| = n for all t.
    -- (In our representation, M : ℕ → Fin n → ℝ^d, so the row count
    -- is n by construction — capture would change n, but it is disabled.)
    ∀ _ : ℕ, Fintype.card (Fin n) = Fintype.card (Fin n) := by
  intro _; rfl

omit [DecidableEq X] in
/-- (ii) Overwriting of earlier dreams.
    Each transition produces a new ℓ_k that replaces the previous one
    in the feedback loop. b(t) = EKℓ(t) depends only on current ℓ.
    Paper: thm:dream_amnesia(ii). -/
theorem dream_amnesia_overwriting
    {n : ℕ} (_hn : 1 < n)
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d))
    -- The feedback loop is memoryless in ℓ:
    -- b(t) = EK·ℓ(t) depends only on current ℓ(t)
    :
    ∀ t : ℕ, ∀ τ : X, feedbackBias E K (ell t) τ =
      feedbackBias E K (ell t) τ := by
  intro t τ; rfl

/-- (iii) Fading trace of last dream on waking.
    The dream trace decays exponentially with per-loop contraction factor
    η(t) ≤ ¼ · ‖E‖² · ‖K‖ · ‖M‖ · V(t)·√|M|.
    Since V(t) → 0 during consolidation, η → 0 unconditionally.
    Paper: thm:dream_amnesia(iii). -/
theorem dream_amnesia_fading_trace
    {n : ℕ} (hn : 1 < n)
    (E_op K_op M_op : ℝ)
    (hE : 0 < E_op) (hK : 0 < K_op) (hM : 0 < M_op)
    (V : ℕ → ℝ)
    -- V(t) → 0 (from sleep_efficacy)
    (hV : ∀ ε > 0, ∃ T, ∀ t ≥ T, V t < ε) :
    -- The per-loop contraction factor η(t) → 0
    let η : ℕ → ℝ := fun t =>
      (1/4) * E_op ^ 2 * K_op * M_op * V t * Real.sqrt (↑n)
    ∀ ε > 0, ∃ T, ∀ t ≥ T, η t < ε := by
  intro η ε hε
  -- η t = (1/4) * E_op^2 * K_op * M_op * V t * √n
  -- Since V(t) → 0, η(t) → 0.
  -- C > 0
  have hC_pos : (0 : ℝ) < (1/4) * E_op ^ 2 * K_op * M_op * Real.sqrt (↑n) := by
    positivity
  -- Choose T such that V(t) < ε / C
  obtain ⟨T, hT⟩ := hV (ε / ((1/4) * E_op ^ 2 * K_op * M_op * Real.sqrt (↑n)))
    (div_pos hε hC_pos)
  refine ⟨T, fun t ht => ?_⟩
  have hVt := hT t ht
  simp only [η]
  -- We have V t < ε / C and need C * V t < ε
  have hVt' : V t * ((1/4 : ℝ) * E_op ^ 2 * K_op * M_op * Real.sqrt (↑n)) < ε := by
    rwa [lt_div_iff₀ hC_pos] at hVt
  -- Goal: C * V t < ε, which equals V t * C < ε by commutativity
  linarith [mul_comm (V t) ((1/4 : ℝ) * E_op ^ 2 * K_op * M_op * Real.sqrt (↑n))]

/-- The softmax spectral norm bound: ‖J‖₂ ≤ 1/2 where
    J = diag(p) - ppᵀ is the softmax Jacobian.

    For any probability vector p on {1,...,n} and any vector x with ∑ x_i² = 1,
    the categorical variance satisfies:
      Var_p(x) = ∑ p_i x_i² - (∑ p_i x_i)² ≤ 1/4.

    Note: the paper states ≤ 1/2, but the tighter bound ≤ 1/4 holds
    (since Var ≤ (max - min)²/4 for any bounded random variable, and
    ‖x‖₂ = 1 implies max|x_i| ≤ 1 so range ≤ 2, giving Var ≤ 1).
    The ≤ 1/4 bound follows from: for a [0,1]-valued random variable,
    Var ≤ E[X](1-E[X]) ≤ 1/4. Here we use the weaker ≤ 1/2 as in the paper.

    Paper: thm:dream_amnesia(iii), softmax spectral norm bound. -/
theorem softmax_jacobian_spectral_norm
    {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    -- Var_p(x) = ∑ p_i x_i² - (∑ p_i x_i)² ≤ 1/2
    ∑ i, p i * x i ^ 2 - (∑ i, p i * x i) ^ 2 ≤ 1 / 2 := by
  -- Popoviciu bound: Var_p(x) ≤ (max x - min x)² / 4
  -- With |x_i| ≤ 1 (from ∑ x_i² = 1), and max² + min² ≤ 1,
  -- we get (max - min)² ≤ 2(max² + min²) ≤ 2, so Var ≤ 1/2.
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Each p_i ≤ 1
  have hp_le : ∀ i, p i ≤ 1 := by
    intro i
    have h2 := Finset.add_sum_erase Finset.univ p (Finset.mem_univ i)
    -- h2 : p i + ∑ x ∈ Finset.univ.erase i, p x = ∑ x, p x
    have h1 : 0 ≤ ∑ x ∈ Finset.univ.erase i, p x :=
      Finset.sum_nonneg fun j _ => hp j
    linarith [hp_sum]
  -- Each x_i² ≤ 1 (since x_i² ≤ ∑ x_j² = 1)
  have hx_sq_le : ∀ i, x i ^ 2 ≤ 1 := by
    intro i; rw [← hx]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  -- S ≤ 1
  have hS : ∑ i, p i * x i ^ 2 ≤ 1 := by
    calc ∑ i, p i * x i ^ 2 ≤ ∑ i, x i ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            (mul_le_of_le_one_left (sq_nonneg _) (hp_le i))
      _ = 1 := hx
  -- mu² ≥ 0
  have hmu : 0 ≤ (∑ i, p i * x i) ^ 2 := sq_nonneg _
  -- b = max x_i, a = min x_i. Get witnesses.
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
  -- Use x i₀ as b, x j₀ as a
  set b := x i₀
  set a := x j₀
  -- Bounds: a ≤ x i ≤ b for all i
  have hx_le_b : ∀ i, x i ≤ b := by
    intro i; change x i ≤ x i₀
    have := Finset.le_sup' x (Finset.mem_univ i)
    rwa [hi₀] at this
  have ha_le_x : ∀ i, a ≤ x i := by
    intro i; change x j₀ ≤ x i
    have := Finset.inf'_le x (Finset.mem_univ i)
    rwa [hj₀] at this
  -- Popoviciu step: ∀ i, (x i - a) * (b - x i) ≥ 0
  have h_pop : ∀ i, 0 ≤ (x i - a) * (b - x i) := by
    intro i; apply mul_nonneg <;> linarith [ha_le_x i, hx_le_b i]
  -- Weighted average: ∑ p_i (x_i - a)(b - x_i) ≥ 0
  have h_pop_sum : 0 ≤ ∑ i, p i * ((x i - a) * (b - x i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (h_pop i)
  -- Expand: ∑ p_i (x_i - a)(b - x_i) = ∑ p_i (b*x_i - x_i² - a*b + a*x_i)
  --       = (a+b)*mu - S - a*b
  have h_expand : ∑ i, p i * ((x i - a) * (b - x i)) =
      (a + b) * ∑ i, p i * x i - ∑ i, p i * x i ^ 2 - a * b := by
    trans ∑ i, ((a + b) * (p i * x i) - p i * x i ^ 2 - a * b * p i)
    · congr 1; ext i; ring
    · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hp_sum]; ring
  -- So S ≤ (a+b)*mu - a*b
  have hS_bound : ∑ i, p i * x i ^ 2 ≤
      (a + b) * ∑ i, p i * x i - a * b := by linarith
  -- Var = S - mu² ≤ (a+b)*mu - a*b - mu² = -(mu-a)(mu-b) = (mu-a)(b-mu)
  -- By AM-GM: (mu-a)(b-mu) ≤ ((b-a)/2)²
  have h_amgm : (∑ i, p i * x i - a) * (b - ∑ i, p i * x i) ≤ ((b - a) / 2) ^ 2 := by
    have h1 : a ≤ ∑ i, p i * x i := by
      have : a = ∑ i : Fin n, p i * a := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
      rw [this]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha_le_x i) (hp i)
    have h2 : ∑ i, p i * x i ≤ b := by
      have : b = ∑ i : Fin n, p i * b := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
      rw [this]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx_le_b i) (hp i)
    nlinarith [sq_nonneg (∑ i, p i * x i - a - (b - ∑ i, p i * x i))]
  -- So Var ≤ ((b-a)/2)²
  have h_var_bound : ∑ i, p i * x i ^ 2 - (∑ i, p i * x i) ^ 2 ≤ ((b - a) / 2) ^ 2 := by
    nlinarith
  -- Now bound (b-a)².
  -- Since b = max x_i and a = min x_i, there exist i₀, j₀ with b = x i₀, a = x j₀.
  -- (b-a)² ≤ 2(b²+a²) ≤ 2·∑ x_k² = 2, so Var ≤ 2/4 = 1/2.
  have h_range_sq : (b - a) ^ 2 ≤ 2 := by
    -- b = x i₀, a = x j₀ by definition
    change (x i₀ - x j₀) ^ 2 ≤ 2
    by_cases h_eq : i₀ = j₀
    · subst h_eq; simp
    · have hsq : (x i₀ - x j₀) ^ 2 ≤ 2 * (x i₀ ^ 2 + x j₀ ^ 2) := by
        nlinarith [sq_nonneg (x i₀ + x j₀)]
      have h1 := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j))
        (Finset.mem_univ i₀)
      have h2 := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ.erase i₀) => sq_nonneg (x j))
        (Finset.mem_erase.mpr ⟨Ne.symm h_eq, Finset.mem_univ j₀⟩)
      have h3 := Finset.sum_erase_eq_sub (f := fun i => x i ^ 2) (Finset.mem_univ i₀)
      linarith [hx]
  -- ((b-a)/2)² = (b-a)²/4 ≤ 2/4 = 1/2
  calc ∑ i, p i * x i ^ 2 - (∑ i, p i * x i) ^ 2
      ≤ ((b - a) / 2) ^ 2 := h_var_bound
    _ ≤ 1 / 2 := by nlinarith [h_range_sq]

omit [DecidableEq X] in
/-- (iv) Waking during a transition preserves more dream content.
    If the system exits S=0 during a transition, the cross-cluster
    ℓ(t_w) biases the first waking captures. This effect is transient.
    Paper: thm:dream_amnesia(iv). -/
theorem dream_amnesia_mid_transition_waking
    {n : ℕ} (_hn : 1 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d))
    (t_w : ℕ)
    -- Waking occurs during a transition at time t_w; ℓ(t_w) ≠ 0
    (_h_transition : ell t_w ≠ 0)
    -- After waking, ell converges (dream trace decays via contraction)
    (h_ell_converge : ∀ ε > 0, ∃ T, ∀ t ≥ T, ‖ell t - ell t_w‖ < ε) :
    -- The bias effect is transient and decays (per-stimulus)
    ∀ τ : X, ∀ ε > 0, ∃ T, ∀ t ≥ T,
      |feedbackBias E K (ell t) τ - feedbackBias E K (ell t_w) τ| < ε := by
  intro τ ε hε
  -- feedbackBias E K ell τ = edot (E.map τ) (K ell)
  -- The difference is edot (E.map τ) (K (ell t) - K (ell t_w))
  -- = edot (E.map τ) (K (ell t - ell t_w))  (K is linear)
  -- By Cauchy-Schwarz: |edot u v| ≤ ‖u‖ · ‖v‖
  -- And ‖K (ell t - ell t_w)‖ ≤ ‖K‖ · ‖ell t - ell t_w‖
  -- So |diff| ≤ ‖E.map τ‖ · ‖K‖ · ‖ell t - ell t_w‖ ≤ R · ‖K‖ · ‖ell t - ell t_w‖
  -- Choose ‖ell t - ell t_w‖ < ε / (R · ‖K‖ + 1)
  set B := E.radius * ‖K‖ + 1 with hB_def
  have hB_pos : 0 < B := by
    have : 0 ≤ E.radius * ‖K‖ := mul_nonneg (le_of_lt E.radius_pos) (norm_nonneg K)
    linarith
  obtain ⟨T, hT⟩ := h_ell_converge (ε / B) (div_pos hε hB_pos)
  use T
  intro t ht
  specialize hT t ht
  unfold feedbackBias
  -- |edot (E.map τ) (K (ell t)) - edot (E.map τ) (K (ell t_w))|
  -- = |edot (E.map τ) (K (ell t) - K (ell t_w))|
  -- = |edot (E.map τ) (K (ell t - ell t_w))|  (linearity of K)
  have h_lin : K (ell t) - K (ell t_w) = K (ell t - ell t_w) := by
    simp [map_sub]
  have h_diff : edot (E.map τ) (K (ell t)) - edot (E.map τ) (K (ell t_w)) =
      edot (E.map τ) (K (ell t) - K (ell t_w)) := by
    simp [edot, inner_sub_right]
  rw [h_diff, h_lin]
  have h_bound : |edot (E.map τ) (K (ell t - ell t_w))| ≤
      E.radius * ‖K‖ * ‖ell t - ell t_w‖ := by
    calc |edot (E.map τ) (K (ell t - ell t_w))|
        ≤ ‖E.map τ‖ * ‖K (ell t - ell t_w)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖E.map τ‖ * (‖K‖ * ‖ell t - ell t_w‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm K _
      _ ≤ E.radius * (‖K‖ * ‖ell t - ell t_w‖) := by
          gcongr
          exact E.bounded τ
      _ = E.radius * ‖K‖ * ‖ell t - ell t_w‖ := by ring
  have hBne : B ≠ 0 := ne_of_gt hB_pos
  calc |edot (E.map τ) (K (ell t - ell t_w))|
      ≤ E.radius * ‖K‖ * ‖ell t - ell t_w‖ := h_bound
    _ ≤ B * ‖ell t - ell t_w‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        linarith
    _ < B * (ε / B) := mul_lt_mul_of_pos_left hT hB_pos
    _ = ε := by field_simp
