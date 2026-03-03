/-
  SleepLoop/Core/SelfLimiting.lean

  Corollary 18 (cor:selflimiting): Vanishing contraction rate.
  Under fixed query + no capture, gamma(t) -> 0 as t -> infinity.
  As M converges, retrieval weights equalize, so blend rates vanish.
  Level: 𝒜₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.Convergence
import SleepLoop.Core.ContractionRate
import SleepLoop.Core.BlendRateBounds
import Mathlib.Topology.UniformSpace.HeineCantor

open Finset BigOperators

/-! ## Self-Limiting Consolidation -/

variable {d n : ℕ}

/-- Auxiliary: the contraction rate is bounded above by the maximum blend rate
    over non-anchor indices.

    Since γ = min_{j≠v} λ_j · (1 - √(1 - α_v^(j))) and each factor
    (1 - √(1 - α_v^(j))) ∈ [0,1], we get γ ≤ min_{j≠v} λ_j ≤ max_{j≠v} λ_j. -/
theorem contractionRate_le_sup_blendRate
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n)
    (hw_pos : ∀ k, 0 < w k) :
    contractionRate φ br w q M v hn ≤
      Finset.sup' (Finset.univ.erase v) (erase_v_nonempty hn v)
        (fun j => consolidationBlendRates br w (by omega) j) := by
  -- Strategy: For each j ≠ v, the j-th factor satisfies
  --   λ_j · (1 - √(1 - α_v^(j))) ≤ λ_j · 1 = λ_j ≤ sup' λ
  -- Since γ = inf' of these products, γ ≤ any single product, hence γ ≤ sup' λ.
  have hne : (Finset.univ.erase v : Finset (Fin n)).Nonempty :=
    erase_v_nonempty hn v
  have hj₀ := hne.choose_spec
  set j₀ := hne.choose
  -- γ ≤ product term for j₀
  have h_gamma_le_term : contractionRate φ br w q M v hn ≤
      consolidationBlendRates br w (by omega) j₀ *
        (1 - Real.sqrt (1 - φ (fun k => edot (M j₀ + q) (M k)) v)) := by
    unfold contractionRate; simp only []
    exact Finset.inf'_le _ hj₀
  -- The (1 - √(1-α)) factor ≤ 1
  have h_factor_le1 :
      1 - Real.sqrt (1 - φ (fun k => edot (M j₀ + q) (M k)) v) ≤ 1 := by
    linarith [Real.sqrt_nonneg (1 - φ (fun k => edot (M j₀ + q) (M k)) v)]
  -- Blend rate ≥ 0
  have h_rate_nn : 0 ≤ consolidationBlendRates br w (by omega : 0 < n) j₀ :=
    (blend_rate_range br w (by omega) (fun k => le_of_lt (hw_pos k))
      ⟨v, hw_pos v⟩ j₀).1
  -- Chain: γ ≤ λ_{j₀} · f_{j₀} ≤ λ_{j₀} ≤ sup' λ
  calc contractionRate φ br w q M v hn
      ≤ consolidationBlendRates br w (by omega) j₀ *
          (1 - Real.sqrt (1 - φ (fun k => edot (M j₀ + q) (M k)) v)) :=
        h_gamma_le_term
    _ ≤ consolidationBlendRates br w (by omega) j₀ * 1 :=
        mul_le_mul_of_nonneg_left h_factor_le1 h_rate_nn
    _ = consolidationBlendRates br w (by omega) j₀ := mul_one _
    _ ≤ Finset.sup' (Finset.univ.erase v) hne
          (fun j => consolidationBlendRates br w (by omega) j) :=
        Finset.le_sup' _ hj₀

/-- Auxiliary: the contraction rate is always non-negative.
    Each factor in the min is a product of non-negatives:
    λ_j ≥ 0 (blend rate range) and (1 - √(1-α)) ≥ 0 (since α ∈ [0,1]). -/
theorem contractionRate_nonneg
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n)
    (hv : ∀ k, w k ≤ w v)
    (hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k) :
    0 ≤ contractionRate φ br w q M v hn :=
  le_of_lt (contraction_rate_pos φ br w q M hn v hv hv_unique hw_pos)

/-! ### Justification: Deriving blend-rate vanishing from convergence

The paper's proof of Corollary 18 (cor:selflimiting) does not assume
`h_blend_vanish` as a primitive hypothesis.  Instead it derives it from:

  (1) Weights come from retrieval: `w(t) = phi(q . M(t)^T)`.
  (2) V(t) → 0, so `‖M(t)(j) - M(t)(v)‖ → 0` for all j.
  (3) Score differences `q . m_j(t) - q . m_v(t) → 0` (Cauchy-Schwarz).
  (4) phi is continuous and score-symmetric (`s i = s j → phi(s) i = phi(s) j`),
      so weight differences `phi(s_t)(v) - phi(s_t)(j) → 0` (uniform continuity
      on the compact box of score vectors).
  (5) Since `phi(s_t)(v) ≥ 1/n`, the weight ratio `phi(s_t)(j) / phi(s_t)(v) → 1`.
  (6) By continuity of `br.fn` and `br.fn(1) = 0`, the blend rate → 0.
  (7) The sup over finitely many indices (each → 0) also → 0.

The theorem `blend_vanish_from_convergence` below formalizes this derivation.
The main theorem `contraction_rate_vanishes` retains `h_blend_vanish` as an
explicit hypothesis for modularity.
-/

/-- **Justification lemma (paper derivation).**
    When weights come from retrieval `w(t) = phi(q . M(t)^T)` applied to
    a bounded trajectory with V(t) → 0, the blend-rate vanishing hypothesis
    `h_blend_vanish` holds automatically.

    Hypotheses:
    - `h_retrieval`: weights are `phi(q . M(t)^T)` (functional dependence on M)
    - `h_sym`: phi is score-symmetric (equal scores give equal weights)
    - `hV_zero`: V(t) → 0 (all impressions converge to anchor)
    - `h_bounded`: M(t) is bounded in norm by R

    The paper derives this from: phi continuous and score-symmetric
    (satisfied by softmax and all natural A+ maps), V(t) → 0 (Corollary 17),
    and bounded trajectories. -/
-- set_option maxHeartbeats 800000 in
theorem blend_vanish_from_convergence
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n) (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (h_retrieval : ∀ t k, w t k = φ (fun j => edot q (M t j)) k)
    (hv : ∀ t k, w t k ≤ w t v)
    (hw_pos : ∀ t k, 0 < w t k)
    (h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R)
    -- phi sends equal-score vectors to equal weights (softmax satisfies this)
    (h_sym : ∀ (s : Fin n → ℝ) (i j : Fin n), s i = s j → φ s i = φ s j)
    -- V(t) → 0 (Corollary 17)
    (hV_zero : Filter.Tendsto (fun t => lyapunovV (M t) v hn)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun t => Finset.sup' (Finset.univ.erase v) (erase_v_nonempty hn v)
        (fun j => consolidationBlendRates br (w t) (by omega) j))
      Filter.atTop (nhds 0) := by
  -- We prove sup'_{j!=v} blend_rate(t)(j) -> 0 via Metric.tendsto_atTop:
  -- for each eps > 0, we find N such that for t >= N, every blend rate < eps.
  obtain ⟨R, hR⟩ := h_bounded
  have hne : (Finset.univ.erase v : Finset (Fin n)).Nonempty :=
    erase_v_nonempty hn v
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  set scores : ℕ → Fin n → ℝ := fun t j => edot q (M t j)
  set scores_const : ℕ → Fin n → ℝ := fun t _ => edot q (M t v)
  -- sup w t = w t v (v is the anchor)
  have h_sup_eq : ∀ t, Finset.sup' Finset.univ Finset.univ_nonempty (w t) = w t v := by
    intro t; apply le_antisymm
    · exact Finset.sup'_le _ _ (fun k _ => hv t k)
    · exact Finset.le_sup' (w t) (Finset.mem_univ v)
  -- Compact box containing all score vectors
  set B := max (‖q‖ * R) 0
  set box := Set.pi Set.univ (fun (_ : Fin n) => Set.Icc (-B) B)
  have hbox_compact : IsCompact box := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hscores_in_box : ∀ t, scores t ∈ box := by
    intro t i _; simp only [Set.mem_Icc]
    have h1 : |edot q (M t i)| ≤ ‖q‖ * ‖M t i‖ := abs_real_inner_le_norm q (M t i)
    have h2 : ‖q‖ * ‖M t i‖ ≤ ‖q‖ * R :=
      mul_le_mul_of_nonneg_left (hR t i) (norm_nonneg q)
    constructor <;> linarith [abs_le.mp (le_trans h1 (le_trans h2 (le_max_left (‖q‖ * R) 0)))]
  have hconst_in_box : ∀ t, scores_const t ∈ box := by
    intro t i _; simp only [Set.mem_Icc, scores_const]
    have h1 : |edot q (M t v)| ≤ ‖q‖ * ‖M t v‖ := abs_real_inner_le_norm q (M t v)
    have h2 : ‖q‖ * ‖M t v‖ ≤ ‖q‖ * R :=
      mul_le_mul_of_nonneg_left (hR t v) (norm_nonneg q)
    constructor <;> linarith [abs_le.mp (le_trans h1 (le_trans h2 (le_max_left (‖q‖ * R) 0)))]
  -- phi uniformly continuous on box (Heine-Cantor)
  have hφ_uc : UniformContinuousOn φ box :=
    hbox_compact.uniformContinuousOn_of_continuous PositiveSimplexMap.cont.continuousOn
  -- phi(s_t)(v) >= 1/n (v is the max weight, sum of n weights = 1)
  have h_phi_v_lower : ∀ t, (1 : ℝ) / n ≤ φ (scores t) v := by
    intro t
    have h_max : ∀ k, φ (scores t) k ≤ φ (scores t) v := by
      intro k; rw [← h_retrieval t k, ← h_retrieval t v]; exact hv t k
    have : ∑ k : Fin n, φ (scores t) k ≤ n * φ (scores t) v :=
      (Finset.sum_le_sum (fun k _ => h_max k)).trans
        (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
    rw [div_le_iff₀ hn_pos, mul_comm]
    linarith [SimplexMap.sum_one (φ := φ) (scores t)]
  -- Main epsilon-delta argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1: Get eta from continuity of br.fn at 1 with br.fn(1) = 0
  have hbr_cont_at : Filter.Tendsto br.fn (nhds 1) (nhds 0) := by
    rw [← br.at_one]; exact br.continuous_fn.continuousAt
  have hbr_evt := Metric.tendsto_nhds.mp hbr_cont_at ε hε
  rw [Metric.eventually_nhds_iff] at hbr_evt
  obtain ⟨η, hη_pos, hη_spec⟩ := hbr_evt
  -- Step 2: Get delta_phi from uniform continuity of phi for target eta/(2n)
  have h_target : (0 : ℝ) < η / (2 * n) :=
    div_pos hη_pos (mul_pos (by norm_num) hn_pos)
  obtain ⟨δ_phi, hδ_phi_pos, hδ_phi⟩ :=
    (Metric.uniformContinuousOn_iff.mp hφ_uc) (η / (2 * n)) h_target
  -- Step 3: V(t) -> 0 implies dist(scores t, scores_const t) < delta_phi eventually
  have h_score_dist_small : ∃ N, ∀ t ≥ N,
      dist (scores t) (scores_const t) < δ_phi := by
    by_cases hq_zero : ‖q‖ = 0
    · refine ⟨0, fun t _ => ?_⟩
      have : scores t = scores_const t := by
        ext j; change edot q (M t j) = edot q (M t v)
        have hq : q = 0 := norm_eq_zero.mp hq_zero
        simp [edot, hq, inner_zero_left]
      rw [this, dist_self]; exact hδ_phi_pos
    · have hq_pos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hq_zero)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hV_zero
        (δ_phi / ‖q‖) (div_pos hδ_phi_pos hq_pos)
      refine ⟨N, fun t ht => ?_⟩
      rw [dist_pi_lt_iff hδ_phi_pos]
      intro j
      rw [Real.dist_eq]
      have key : edot q (M t j) - edot q (M t v) = edot q (M t j - M t v) := by
        simp [edot, inner_sub_right]
      rw [show scores t j - scores_const t j = edot q (M t j) - edot q (M t v) from rfl, key]
      calc |edot q (M t j - M t v)|
          ≤ ‖q‖ * ‖M t j - M t v‖ := abs_real_inner_le_norm q _
        _ ≤ ‖q‖ * lyapunovV (M t) v hn := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
            by_cases hiv : j = v
            · rw [hiv, sub_self, norm_zero]; exact lyapunovV_nonneg (M t) v hn
            · exact Finset.le_sup' (fun k => ‖M t k - M t v‖)
                (Finset.mem_erase.mpr ⟨hiv, Finset.mem_univ j⟩)
        _ < ‖q‖ * (δ_phi / ‖q‖) := by
            apply mul_lt_mul_of_pos_left _ hq_pos
            have h := hN t ht
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (lyapunovV_nonneg _ _ _)] at h; exact h
        _ = δ_phi := mul_div_cancel₀ δ_phi (ne_of_gt hq_pos)
  -- Step 4: Get N and prove the bound
  obtain ⟨N, hN⟩ := h_score_dist_small
  refine ⟨N, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have h_blend_nn : ∀ j, 0 ≤ consolidationBlendRates br (w t) (by omega : 0 < n) j :=
    fun j => (blend_rate_range br (w t) (by omega) (fun k => le_of_lt (hw_pos t k))
      ⟨v, hw_pos t v⟩ j).1
  rw [abs_of_nonneg (le_trans (h_blend_nn hne.choose) (Finset.le_sup' _ hne.choose_spec))]
  -- Each blend rate for j != v is < eps
  rw [Finset.sup'_lt_iff]
  intro j hj
  have hjv : j ≠ v := (Finset.mem_erase.mp hj).1
  change consolidationBlendRates br (w t) (by omega) j < ε
  -- Unfold: blend_rate = br.fn(w_j / w_max) = br.fn(phi(s)(j) / phi(s)(v))
  unfold consolidationBlendRates
  rw [h_sup_eq t, h_retrieval t j, h_retrieval t v]
  have h_phiv_pos := PositiveSimplexMap.pos (φ := φ) (scores t) v
  have h_diff_nn : 0 ≤ φ (scores t) v - φ (scores t) j := by
    rw [← h_retrieval t j, ← h_retrieval t v]; linarith [hv t j]
  -- dist(phi(s_t), phi(s'_t)) < eta/(2n) by uniform continuity
  have h_phi_dist : dist (φ (scores t)) (φ (scores_const t)) < η / (2 * n) :=
    hδ_phi _ (hscores_in_box t) _ (hconst_in_box t) (hN t ht)
  -- phi(s'_t)(j) = phi(s'_t)(v) by symmetry
  have h_sym_eq : φ (scores_const t) j = φ (scores_const t) v :=
    h_sym (scores_const t) j v rfl
  -- Triangle: phi(s)(v) - phi(s)(j) < eta/n
  have h_diff_small : φ (scores t) v - φ (scores t) j < η / n := by
    calc φ (scores t) v - φ (scores t) j
        = (φ (scores t) v - φ (scores_const t) v) +
          (φ (scores_const t) j - φ (scores t) j) := by rw [h_sym_eq]; ring
      _ ≤ |φ (scores t) v - φ (scores_const t) v| +
          |φ (scores_const t) j - φ (scores t) j| :=
        add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ dist (φ (scores t)) (φ (scores_const t)) +
          dist (φ (scores t)) (φ (scores_const t)) := by
        apply add_le_add
        · exact dist_le_pi_dist (φ (scores t)) (φ (scores_const t)) v
        · rw [abs_sub_comm]
          exact dist_le_pi_dist (φ (scores t)) (φ (scores_const t)) j
      _ < η / (2 * n) + η / (2 * n) := add_lt_add h_phi_dist h_phi_dist
      _ = η / n := by ring
  -- (phi_v - phi_j) / phi_v <= n * (phi_v - phi_j) < eta
  have h_ratio_close : dist (φ (scores t) j / φ (scores t) v) 1 < η := by
    rw [Real.dist_eq, abs_sub_comm]
    have h_ratio_le1 : φ (scores t) j / φ (scores t) v ≤ 1 :=
      div_le_one_of_le₀ (by rw [← h_retrieval t j, ← h_retrieval t v]; exact hv t j)
        (le_of_lt h_phiv_pos)
    have h_ratio_nn : 0 ≤ φ (scores t) j / φ (scores t) v :=
      div_nonneg (le_of_lt (PositiveSimplexMap.pos (φ := φ) (scores t) j)) (le_of_lt h_phiv_pos)
    have h_one_sub_nn : 0 ≤ 1 - φ (scores t) j / φ (scores t) v := by linarith [h_ratio_le1]
    rw [abs_of_nonneg h_one_sub_nn]
    calc 1 - φ (scores t) j / φ (scores t) v
        = (φ (scores t) v - φ (scores t) j) / φ (scores t) v := by
            rw [sub_div, div_self (ne_of_gt h_phiv_pos)]
      _ ≤ (φ (scores t) v - φ (scores t) j) / (1 / ↑n) := by
          apply div_le_div_of_nonneg_left h_diff_nn (by positivity) (h_phi_v_lower t)
      _ = ↑n * (φ (scores t) v - φ (scores t) j) := by field_simp
      _ < ↑n * (η / ↑n) :=
          mul_lt_mul_of_pos_left h_diff_small hn_pos
      _ = η := mul_div_cancel₀ η (Nat.cast_ne_zero.mpr (by omega))
  -- br.fn applied to ratio gives < eps
  have h1 := hη_spec h_ratio_close
  rw [Real.dist_eq, sub_zero] at h1
  rwa [abs_of_nonneg (br.maps_to _
    (div_nonneg (le_of_lt (PositiveSimplexMap.pos (φ := φ) (scores t) j)) (le_of_lt h_phiv_pos))
    (div_le_one_of_le₀ (by rw [← h_retrieval t j, ← h_retrieval t v]; exact hv t j)
      (le_of_lt h_phiv_pos))).1] at h1

/-- cor:selflimiting: The contraction rate γ(t) → 0 as t → ∞.

    Paper proof (Corollary 18):
    γ(t) = min_{j≠v} λ_j(t) · (1 - √(1 - α_v^(j)(t))).
    The factor (1 - √(1 - α_v^(j))) ∈ [0,1] is bounded.
    As V(t) → 0, M_j → M_v, scores equalize, and the paper argues
    w_j/w_v → 1 (from w = φ(q·M^T)), so λ_j = br(w_j/w_v) → br(1) = 0.
    Product of (→ 0) times (bounded) → 0; min of finitely many → 0.

    The hypothesis h_blend_vanish encodes the paper's implicit derivation
    that w = φ(q · M^T): as V → 0, scores equalize, weights equalize,
    and the maximum blend rate (over non-anchor indices) → 0.
    Given this, the squeeze argument
      0 ≤ γ(t) ≤ sup_{j≠v} λ_j(t) → 0
    closes the proof. -/
theorem contraction_rate_vanishes
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n)
    (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (hv : ∀ t k, w t k ≤ w t v)
    (hv_unique : ∀ t k, k ≠ v → w t k < w t v)
    (hw_pos : ∀ t k, 0 < w t k)
    -- The paper derives blend-rate vanishing from w = φ(q · M^T) and continuity
    -- of φ: as V → 0, scores equalize, w_j/w_v → 1, br(w_j/w_v) → br(1) = 0.
    (h_blend_vanish : Filter.Tendsto
      (fun t => Finset.sup' (Finset.univ.erase v) (erase_v_nonempty hn v)
        (fun j => consolidationBlendRates br (w t) (by omega) j))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun t => contractionRate φ br (w t) q (M t) v (by omega))
      Filter.atTop (nhds 0) := by
  -- Squeeze: 0 ≤ γ(t) ≤ sup_{j≠v} λ_j(t) → 0
  apply squeeze_zero
  · -- Lower bound: γ(t) ≥ 0
    intro t
    exact contractionRate_nonneg φ br (w t) q (M t) v hn (hv t)
      (hv_unique t) (hw_pos t)
  · -- Upper bound: γ(t) ≤ sup_{j≠v} λ_j(t)
    intro t
    exact contractionRate_le_sup_blendRate φ br (w t) q (M t) v hn
      (hw_pos t)
  · -- Convergence: sup_{j≠v} λ_j(t) → 0
    exact h_blend_vanish
