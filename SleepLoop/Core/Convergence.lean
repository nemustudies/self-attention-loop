/-
  SleepLoop/Core/Convergence.lean

  Corollary 17 (cor:sleep): Convergence under repeated consolidation.
  D(t) -> 0: all impressions converge to the anchor v.
  Uses compactness (lem:hull) + Lyapunov (lem:lyapunov).
  Level: 𝒜₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.Lyapunov
import SleepLoop.Core.ContractionRate
import SleepLoop.Core.ConvexHullInvariance
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic

open Finset BigOperators

/-! ## Convergence Under Repeated Consolidation -/

variable {d n : ℕ}

/-- Auxiliary: lyapunovV is always non-negative (sup of norms). -/
theorem lyapunovV_nonneg
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) :
    0 ≤ lyapunovV M v hn := by
  unfold lyapunovV
  obtain ⟨j, hj⟩ := erase_v_nonempty hn v
  exact le_trans (norm_nonneg _) (Finset.le_sup' (fun j => ‖M j - M v‖) hj)

/-- Auxiliary: if lyapunovV = 0, all impressions equal the anchor. -/
theorem lyapunovV_eq_zero_iff
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) :
    lyapunovV M v hn = 0 ↔ ∀ j, j ≠ v → M j = M v := by
  constructor
  · intro hV j hjv
    have hmem : j ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hjv, Finset.mem_univ j⟩
    have hle : ‖M j - M v‖ ≤ lyapunovV M v hn := by
      change ‖M j - M v‖ ≤ Finset.sup' _ _ _
      exact Finset.le_sup' (fun j => ‖M j - M v‖) hmem
    rw [hV] at hle
    have h0 : ‖M j - M v‖ = 0 := le_antisymm hle (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  · intro hall
    unfold lyapunovV
    apply le_antisymm
    · apply Finset.sup'_le
      intro j hj
      have hjv := (Finset.mem_erase.mp hj).1
      rw [hall j hjv, sub_self, norm_zero]
    · obtain ⟨k, hk⟩ := erase_v_nonempty hn v
      exact le_trans (norm_nonneg _) (Finset.le_sup' (fun j => ‖M j - M v‖) hk)

/-- Auxiliary: if V = 0, then consolidation preserves V = 0.
    When all impressions equal the anchor, consolidation maps
    everything to the anchor (convex combination of identical points). -/
theorem lyapunovV_zero_preserved
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n) (v : Fin n)
    (hv : ∀ k, w k ≤ w v)
    (hw_pos : 0 < w v)
    (hV_zero : lyapunovV M v hn = 0) :
    lyapunovV (consolidationStep φ br w q M (by omega)) v hn = 0 := by
  rw [lyapunovV_eq_zero_iff] at hV_zero ⊢
  intro j hjv
  set M' := consolidationStep φ br w q M (by omega) with hM'_def
  -- M' v = M v (anchor unchanged)
  have hM'v : M' v = M v :=
    anchor_unchanged_by_consolidation φ br w q M (by omega) v hv hw_pos
  -- Since all M k = M v, the consolidation target T_j = ∑ α_k • M k = ∑ α_k • M v = M v
  have hall : ∀ k, M k = M v := by
    intro k; by_cases hkv : k = v
    · exact hkv ▸ rfl
    · exact hV_zero k hkv
  -- M' j = (1-r) • M j + r • T_j = (1-r) • M v + r • M v = M v
  change M' j = M' v
  rw [hM'v]
  unfold consolidationStep consolidationBlendRates consolidationTarget at hM'_def
  simp only [] at hM'_def
  rw [hM'_def]
  simp only []
  -- T_j = ∑ α_k • M k = ∑ α_k • M v = (∑ α_k) • M v = 1 • M v = M v
  set scores : Fin n → ℝ := fun k => edot (M j + q) (M k) with _scores_def
  set alpha := φ scores with _alpha_def
  have halpha_sum : ∑ k : Fin n, alpha k = 1 := SimplexMap.sum_one scores
  have hT : ∑ k : Fin n, alpha k • M k = M v := by
    have : ∀ k, alpha k • M k = alpha k • M v := fun k => by rw [hall k]
    simp_rw [this, ← Finset.sum_smul, halpha_sum, one_smul]
  rw [hall j, hT]
  -- (1-r) • M v + r • M v = M v
  rw [← add_smul, sub_add_cancel, one_smul]

/-- Helper: geometric contraction forces a sequence to zero.
    If 0 ≤ f(t), f(t+1) ≤ c * f(t) for all t, and 0 ≤ c < 1,
    then f(t) → 0. -/
private theorem geometric_tendsto_zero
    (f : ℕ → ℝ) (c : ℝ)
    (hc_nonneg : 0 ≤ c) (hc_lt : c < 1)
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_step : ∀ t, f (t + 1) ≤ c * f t) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hf_bound : ∀ t, f t ≤ c ^ t * f 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      calc f (n + 1) ≤ c * f n := hf_step n
        _ ≤ c * (c ^ n * f 0) := by
            exact mul_le_mul_of_nonneg_left ih hc_nonneg
        _ = c ^ (n + 1) * f 0 := by ring
  apply squeeze_zero hf_nonneg (fun t => hf_bound t)
  have h1 : Filter.Tendsto (fun t => c ^ t) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc_nonneg hc_lt
  have h2 : Filter.Tendsto (fun t => c ^ t * f 0) Filter.atTop (nhds (0 * f 0)) :=
    h1.mul_const (f 0)
  simp only [zero_mul] at h2
  exact h2

/-! ### Justification: Deriving the weight gap from compactness

The paper's proof of Corollary 17 (cor:sleep) does not assume a uniform
weight gap as a hypothesis.  Instead it derives one from:

  (1) Weights come from retrieval: `w(t) = phi(q . M(t)^T)`, a continuous
      function of M(t).
  (2) M(t) is bounded (lives in conv(E(X))), so the set of possible
      configurations is compact.
  (3) v is the unique score-maximizer under a uniform score gap:
      `q . m_v - q . m_k >= g > 0` for all k != v.
  (4) The weight difference `phi(scores)_v - phi(scores)_k` is a continuous
      function of scores (hence of M), and is positive at every point
      of the compact constraint set (by order-preservation of phi).
  (5) By compactness, the minimum of this difference is attained and
      positive.  Since `phi(s)_v <= 1`, this additive gap implies a
      multiplicative gap: `phi(s)_k <= (1 - eps) * phi(s)_v`.

The theorem `weight_gap_from_retrieval` below formalizes this derivation.
The main convergence theorems (`contraction_rate_uniform_lower_bound`,
`convergence_under_consolidation`, `diameter_converges_to_zero`) retain
`h_weight_gap` as an explicit hypothesis for modularity: callers who
obtain weights from retrieval can use this lemma to discharge it.
-/

/-- **Justification lemma (paper derivation).**
    When weights come from retrieval `w(t) = phi(q . M(t)^T)` applied to
    a bounded trajectory with a uniform score gap, the uniform weight gap
    `h_weight_gap` holds automatically.

    Hypotheses:
    - `h_retrieval`: weights are `phi(q . M(t)^T)` (functional dependence on M)
    - `h_score_gap`: uniform score gap `g > 0` (v always wins by at least g)
    - `h_bounded`: M(t) is bounded in norm by R

    The paper derives the uniform score gap from: fixed query q, v is the
    unique argmax, and M lives in a compact set.  The gap is the minimum
    of `q . (m_v - m_k)` over the compact configuration space, which is
    attained and positive.

    Proof: All score vectors lie in the compact box `[-B', B']^n`.
    The set K_k of score vectors satisfying `s_v - s_k >= g` is a closed
    subset of the box, hence compact.  On K_k, phi(s)_v - phi(s)_k > 0
    (by order-preservation).  By compactness, this difference attains a
    positive minimum eps_k.  Since phi(s)_v <= 1, the additive gap eps_k
    implies `phi(s)_k <= (1 - eps_k) * phi(s)_v`.  Taking the minimum
    over all k != v gives the uniform delta. -/
theorem weight_gap_from_retrieval
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (q : EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n) (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (h_retrieval : ∀ t k, w t k = φ (fun j => edot q (M t j)) k)
    (g : ℝ) (hg : 0 < g)
    (h_score_gap : ∀ t k, k ≠ v → g ≤ edot q (M t v) - edot q (M t k))
    (h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t k, k ≠ v → w t k ≤ (1 - δ) * w t v := by
  obtain ⟨R, hR⟩ := h_bounded
  -- Score vectors lie in the compact box [-B', B']^n
  set B' := max (‖q‖ * R) 0
  set box := Set.pi Set.univ (fun (_ : Fin n) => Set.Icc (-B') B')
  have hbox_compact : IsCompact box := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hscores_in_box : ∀ t, (fun j => edot q (M t j)) ∈ box := by
    intro t i _; simp only [Set.mem_Icc]
    have h1 : |edot q (M t i)| ≤ ‖q‖ * ‖M t i‖ := abs_real_inner_le_norm q (M t i)
    have h2 : ‖q‖ * ‖M t i‖ ≤ ‖q‖ * R :=
      mul_le_mul_of_nonneg_left (hR t i) (norm_nonneg q)
    constructor
    · linarith [abs_le.mp (le_trans h1 (le_trans h2 (le_max_left (‖q‖ * R) 0)))]
    · linarith [abs_le.mp (le_trans h1 (le_trans h2 (le_max_left (‖q‖ * R) 0)))]
  have hφ_cont : Continuous φ := PositiveSimplexMap.cont
  have hne : (Finset.univ.erase v : Finset (Fin n)).Nonempty :=
    erase_v_nonempty hn v
  -- K = box intersect {forall k != v, s_v - s_k >= g} is compact (closed in compact).
  -- On K, d(s) = inf'_{k!=v}(phi(s)_v - phi(s)_k) is continuous and positive.
  -- By compactness, d attains a positive minimum eps, giving the uniform gap.
  set K := box ∩ ⋂ k ∈ Finset.univ.erase v,
    (fun s : Fin n → ℝ => s v - s k) ⁻¹' (Set.Ici g)
  have hK_compact : IsCompact K := by
    apply hbox_compact.inter_right
    apply isClosed_biInter
    intro k _
    exact isClosed_Ici.preimage ((continuous_apply v).sub (continuous_apply k))
  have hK_ne : K.Nonempty := by
    refine ⟨fun j => edot q (M 0 j), hscores_in_box 0, ?_⟩
    simp only [Set.mem_iInter]
    intro k hk
    simp only [Set.mem_preimage, Set.mem_Ici]
    exact h_score_gap 0 k (Finset.ne_of_mem_erase hk)
  have hscores_in_K : ∀ t, (fun j => edot q (M t j)) ∈ K := by
    intro t; refine ⟨hscores_in_box t, ?_⟩
    simp only [Set.mem_iInter]; intro k hk
    simp only [Set.mem_preimage, Set.mem_Ici]
    exact h_score_gap t k (Finset.ne_of_mem_erase hk)
  -- The min-difference function d(s) = inf'_{k!=v} (phi(s)_v - phi(s)_k)
  -- We show it's continuous using Continuous.finset_inf'_apply
  set min_diff : (Fin n → ℝ) → ℝ :=
    fun s => Finset.inf' (Finset.univ.erase v) hne (fun k => φ s v - φ s k)
  have hmd_cont : Continuous min_diff := by
    change Continuous (fun s => (Finset.univ.erase v).inf' hne (fun k => φ s v - φ s k))
    apply Continuous.finset_inf'_apply hne
    intro k _
    exact ((continuous_apply v).comp hφ_cont).sub ((continuous_apply k).comp hφ_cont)
  -- min_diff attains its minimum on K
  obtain ⟨s₀, hs₀_mem, hs₀_min⟩ :=
    hK_compact.exists_isMinOn hK_ne hmd_cont.continuousOn
  set ε := min_diff s₀
  -- epsilon > 0: at s₀, for each k != v, s₀ in K so gap >= g > 0
  have hε_pos : 0 < ε := by
    change 0 < Finset.inf' (Finset.univ.erase v) hne (fun k => φ s₀ v - φ s₀ k)
    rw [Finset.lt_inf'_iff]
    intro k hk
    have hkv : k ≠ v := Finset.ne_of_mem_erase hk
    have hmem_k : g ≤ s₀ v - s₀ k := by
      have h2 := hs₀_mem.2
      simp only [Set.mem_iInter] at h2
      exact (h2 k hk : s₀ ∈ (fun s => s v - s k) ⁻¹' Set.Ici g)
    linarith [PositiveSimplexMap.order_preserving (φ := φ) s₀ v k (show s₀ v > s₀ k by linarith)]
  -- delta = epsilon works
  refine ⟨ε, hε_pos, fun t k hkv => ?_⟩
  rw [h_retrieval t k, h_retrieval t v]
  set s := fun j => edot q (M t j)
  have hmd_bound : ε ≤ min_diff s := hs₀_min (hscores_in_K t)
  have hk_mem : k ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hkv, Finset.mem_univ k⟩
  have hdiff_bound : ε ≤ φ s v - φ s k :=
    le_trans hmd_bound (Finset.inf'_le _ hk_mem)
  have hφv_le1 : φ s v ≤ 1 := SimplexMap.le_one s v
  -- phi(s)_k <= phi(s)_v - eps <= phi(s)_v - eps*phi(s)_v = (1 - eps)*phi(s)_v
  calc φ s k
      ≤ φ s v - ε := by linarith [hdiff_bound]
    _ ≤ φ s v - ε * φ s v := by
        have : ε * φ s v ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left hφv_le1 (le_of_lt hε_pos)
        linarith
    _ = (1 - ε) * φ s v := by ring

/-- Compactness argument: When M is bounded and V(t) ≥ L > 0 for all t,
    the contraction rate γ(t) is uniformly bounded below by some γ₀ > 0.

    Paper proof (cor:sleep): At the limit configuration M*, the query q is
    fixed, scores are well-defined, w_j < w_v for all j ≠ v (by the fixed
    query and positivity of φ), giving λ_j > 0. Combined with α_v^(j) > 0,
    each factor in γ is positive, and by compactness of the bounded set,
    the minimum is attained and positive.

    This is the core compactness step; the rest of cor:sleep follows.

    The hypothesis `h_weight_gap` (uniform weight gap) is required for the
    blend-rate lower bound.  When weights come from retrieval on bounded
    configurations with a uniform score gap, this hypothesis can be
    discharged using `weight_gap_from_retrieval` above. -/
theorem contraction_rate_uniform_lower_bound
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n) (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (hv : ∀ t k, w t k ≤ w t v)
    (hv_unique : ∀ t k, k ≠ v → w t k < w t v)
    (hw_pos : ∀ t k, 0 < w t k)
    (h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R)
    -- Uniform weight gap: weight ratios are bounded away from 1
    (h_weight_gap : ∃ δ : ℝ, 0 < δ ∧ ∀ t k, k ≠ v → w t k ≤ (1 - δ) * w t v) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 ∧
      ∀ t, γ₀ ≤ contractionRate φ br (w t) q (M t) v hn := by
  obtain ⟨R, hR⟩ := h_bounded
  obtain ⟨δ, hδ_pos, hδ_gap⟩ := h_weight_gap
  -- Part 1: Uniform lower bound on blend rates for j ≠ v.
  -- Since w_j ≤ (1-δ) w_v, the ratio w_j/w_v ≤ 1-δ < 1.
  -- br.fn is continuous, positive on [0,1), and [0, 1-δ] is compact.
  -- So br.fn attains a positive minimum lam_min on [0, 1-δ].
  have hδ_le1 : δ ≤ 1 := by
    by_contra h; push_neg at h
    -- Since n ≥ 2, there exists k ≠ v
    obtain ⟨k, hk⟩ := erase_v_nonempty hn v
    have hkv : k ≠ v := (Finset.mem_erase.mp hk).1
    -- w 0 k > 0 but w 0 k ≤ (1 - δ) * w 0 v < 0 since δ > 1 and w 0 v > 0
    have h1 := hδ_gap 0 k hkv
    have h2 := hw_pos 0 k
    have h3 : (1 - δ) * w 0 v < 0 := mul_neg_of_neg_of_pos (by linarith) (hw_pos 0 v)
    linarith
  have h1mδ_nn : 0 ≤ 1 - δ := by linarith
  -- The interval [0, 1-δ] is compact
  have h_Icc_compact : IsCompact (Set.Icc 0 (1 - δ)) := isCompact_Icc
  have h_Icc_ne : (Set.Icc 0 (1 - δ) : Set ℝ).Nonempty :=
    ⟨0, Set.left_mem_Icc.mpr h1mδ_nn⟩
  -- br.fn is continuous
  have hbr_cont : Continuous br.fn := br.continuous_fn
  -- br.fn attains its minimum on [0, 1-δ]
  obtain ⟨r₀, hr₀_mem, hr₀_min⟩ :=
    h_Icc_compact.exists_isMinOn h_Icc_ne hbr_cont.continuousOn
  -- The minimum is positive since br.fn > 0 on [0, 1) and 1-δ < 1
  have hr₀_range : r₀ ∈ Set.Icc 0 (1 - δ) := hr₀_mem
  have hr₀_nn : 0 ≤ r₀ := hr₀_range.1
  have hr₀_lt1 : r₀ < 1 := lt_of_le_of_lt hr₀_range.2 (by linarith)
  set lam_min := br.fn r₀ with hlam_min_def
  have hlam_min_pos : 0 < lam_min := br.pos_interior r₀ hr₀_nn hr₀_lt1
  -- All blend rates for j ≠ v are ≥ lam_min
  have hrate_lower : ∀ t j, j ≠ v →
      lam_min ≤ consolidationBlendRates br (w t) (by omega : 0 < n) j := by
    intro t j hjv
    unfold consolidationBlendRates
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    -- sup' w = w v (since w_k ≤ w_v for all k)
    have h_sup_eq : Finset.sup' Finset.univ Finset.univ_nonempty (w t) = w t v := by
      apply le_antisymm
      · apply Finset.sup'_le; intro k _; exact hv t k
      · exact Finset.le_sup' (w t) (Finset.mem_univ v)
    rw [h_sup_eq]
    -- w_j / w_v is in [0, 1-δ]
    have h_ratio_nn : 0 ≤ w t j / w t v :=
      div_nonneg (le_of_lt (hw_pos t j)) (le_of_lt (hw_pos t v))
    have h_ratio_le : w t j / w t v ≤ 1 - δ := by
      rw [div_le_iff₀ (hw_pos t v)]
      exact hδ_gap t j hjv
    have h_ratio_in : w t j / w t v ∈ Set.Icc 0 (1 - δ) :=
      ⟨h_ratio_nn, h_ratio_le⟩
    exact hr₀_min h_ratio_in
  -- Part 2: Uniform lower bound on φ(scores) v using compactness.
  -- All scores lie in [-B, B] where B = (R + ‖q‖) * R.
  -- The compact box of score vectors has φ(·) v > 0 everywhere,
  -- so the minimum is positive.
  set B := (R + ‖q‖) * R with B_def
  -- B might be negative if R = 0 but that's fine; use max B 0 for the box
  set B' := max B 0 with B'_def
  have hB'_nn : 0 ≤ B' := le_max_right _ _
  -- Compact box for score vectors
  set box := Set.pi Set.univ (fun (_ : Fin n) => Set.Icc (-B') B') with box_def
  have hbox_compact : IsCompact box := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hbox_ne : box.Nonempty :=
    ⟨0, fun _ _ => by simp only [Pi.zero_apply, Set.mem_Icc]; constructor <;> linarith⟩
  -- φ(·) v is continuous
  have hφ_cont : Continuous φ := PositiveSimplexMap.cont
  have hφv_cont : Continuous (fun x : Fin n → ℝ => φ x v) :=
    (continuous_apply v).comp hφ_cont
  -- φ(·) v attains its minimum on the box
  obtain ⟨s₀, hs₀_mem, hs₀_min⟩ :=
    hbox_compact.exists_isMinOn hbox_ne hφv_cont.continuousOn
  set α_min := φ s₀ v with hα_min_def
  have hα_min_pos : 0 < α_min := PositiveSimplexMap.pos s₀ v
  -- All φ(scores_t_j) v ≥ α_min for bounded M
  have hscores_in_box : ∀ t j, (fun k => edot (M t j + q) (M t k)) ∈ box := by
    intro t j i _
    simp only [Set.mem_Icc]
    have h1 : ‖M t j + q‖ ≤ R + ‖q‖ := by
      calc ‖M t j + q‖ ≤ ‖M t j‖ + ‖q‖ := norm_add_le _ _
        _ ≤ R + ‖q‖ := by linarith [hR t j]
    have h2 : |edot (M t j + q) (M t i)| ≤ ‖M t j + q‖ * ‖M t i‖ :=
      abs_real_inner_le_norm _ _
    have h3 : ‖M t j + q‖ * ‖M t i‖ ≤ (R + ‖q‖) * R := by
      apply mul_le_mul h1 (hR t i) (norm_nonneg _)
      linarith [norm_nonneg (M t j + q)]
    constructor
    · linarith [abs_le.mp (le_trans h2 (le_trans h3 (le_max_left B 0)))]
    · linarith [abs_le.mp (le_trans h2 (le_trans h3 (le_max_left B 0)))]
  have hα_lower : ∀ t j, α_min ≤ φ (fun k => edot (M t j + q) (M t k)) v := by
    intro t j; exact hs₀_min (hscores_in_box t j)
  -- Part 3: Combine into a uniform lower bound on contractionRate.
  -- contractionRate = inf'_{j ≠ v} (rates_j * (1 - √(1 - α_v_j)))
  -- Each factor: rates_j ≥ lam_min and α_v_j ≥ α_min, so
  -- 1 - √(1 - α_v_j) ≥ 1 - √(1 - α_min) > 0
  -- Product ≥ lam_min * (1 - √(1 - α_min)) > 0
  have hα_min_le1 : α_min ≤ 1 := SimplexMap.le_one s₀ v
  have h_sqrt_factor_pos : 0 < 1 - Real.sqrt (1 - α_min) := by
    have h1 : 1 - α_min < 1 := by linarith
    have h2 : 0 ≤ 1 - α_min := by linarith
    have h3 : Real.sqrt (1 - α_min) < 1 := by
      calc Real.sqrt (1 - α_min) < Real.sqrt 1 :=
            Real.sqrt_lt_sqrt h2 h1
        _ = 1 := Real.sqrt_one
    linarith
  set γ₀ := lam_min * (1 - Real.sqrt (1 - α_min)) with hγ₀_def
  refine ⟨γ₀, mul_pos hlam_min_pos h_sqrt_factor_pos, ?_, ?_⟩
  · -- γ₀ ≤ 1: since lam_min ≤ 1 and (1 - √(1-α)) ≤ 1
    have hlam_le1 : lam_min ≤ 1 :=
      (br.maps_to r₀ hr₀_nn (le_of_lt hr₀_lt1)).2
    have h_factor_le1 : 1 - Real.sqrt (1 - α_min) ≤ 1 := by
      linarith [Real.sqrt_nonneg (1 - α_min)]
    calc γ₀ = lam_min * (1 - Real.sqrt (1 - α_min)) := rfl
      _ ≤ 1 * 1 := mul_le_mul hlam_le1 h_factor_le1
          (le_of_lt h_sqrt_factor_pos) (by linarith)
      _ = 1 := one_mul 1
  · -- ∀ t, γ₀ ≤ contractionRate ...
    intro t
    unfold contractionRate; simp only []
    -- Need: γ₀ ≤ inf'_{j ≠ v} (rates_j * (1 - √(1 - α_v_j)))
    -- Suffices: γ₀ ≤ each term in the inf'
    apply Finset.le_inf'
    intro j hj
    have hjv : j ≠ v := (Finset.mem_erase.mp hj).1
    -- Lower bound on rates_j
    have h_rate_lb := hrate_lower t j hjv
    -- Lower bound on α_v_j = φ(scores) v
    have h_alpha_lb := hα_lower t j
    -- Lower bound on 1 - √(1 - α_v_j)
    -- Since α_v_j ≥ α_min, we have 1 - α_v_j ≤ 1 - α_min,
    -- so √(1 - α_v_j) ≤ √(1 - α_min), so 1-√(1-α_v_j) ≥ 1-√(1-α_min)
    set α_v_j := φ (fun k => edot (M t j + q) (M t k)) v with _hα_v_j
    have hα_v_j_le1 : α_v_j ≤ 1 := SimplexMap.le_one _ v
    have h_sqrt_mono : Real.sqrt (1 - α_v_j) ≤ Real.sqrt (1 - α_min) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h_factor_lb : 1 - Real.sqrt (1 - α_min) ≤
        1 - Real.sqrt (1 - α_v_j) := by linarith
    -- Product lower bound
    calc γ₀ = lam_min * (1 - Real.sqrt (1 - α_min)) := rfl
      _ ≤ consolidationBlendRates br (w t) (by omega) j *
          (1 - Real.sqrt (1 - α_v_j)) := by
        apply mul_le_mul h_rate_lb h_factor_lb
          (le_of_lt h_sqrt_factor_pos) (le_of_lt (blend_rate_nonanchor_pos
            φ br (w t) (by omega) v j hjv (hv t) (hv_unique t) (hw_pos t)))

/-- cor:sleep: Under A+ with fixed query q and capture disabled,
    V(t) → 0. All impressions converge to the anchor v.

    Proof sketch: V(t) is strictly decreasing and bounded below by 0.
    By compactness (conv(M) ⊆ conv(E(X))), M has a convergent subsequence.
    At any limit with V > 0, the contraction rate γ > 0 forces
    geometric decrease, contradicting the limit. Hence V → 0. -/
theorem convergence_under_consolidation
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n)
    (v : Fin n)
    -- M(t) is the sequence of memory states under iterated consolidation
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    -- w(t) are retrieval weights at each step
    (w : ℕ → Fin n → ℝ)
    -- v is always the anchor (unique max of w)
    (hv : ∀ t k, w t k ≤ w t v)
    (hv_unique : ∀ t k, k ≠ v → w t k < w t v)
    -- weights are positive (needed for lyapunov_strict_decrease)
    (hw_pos : ∀ t k, 0 < w t k)
    -- M evolves by consolidation
    (h_step : ∀ t, M (t + 1) = consolidationStep φ br (w t) q (M t) (by omega))
    -- M is bounded (lives in conv(E(X)))
    (h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R)
    -- Uniform weight gap: see `weight_gap_from_retrieval` for derivation from paper hypotheses
    (h_weight_gap : ∃ δ : ℝ, 0 < δ ∧ ∀ t k, k ≠ v → w t k ≤ (1 - δ) * w t v) :
    Filter.Tendsto (fun t => lyapunovV (M t) v hn) Filter.atTop (nhds 0) := by
  -- Set up the Lyapunov sequence
  set V : ℕ → ℝ := fun t => lyapunovV (M t) v hn with V_def
  -- Step 1: V is non-negative
  have hV_nonneg : ∀ t, 0 ≤ V t := fun t => lyapunovV_nonneg (M t) v hn
  -- Step 2: V is non-increasing (antitone)
  have hV_antitone : Antitone V := by
    intro s t hst
    -- Suffices to show V(t+1) ≤ V(t) for all t, then induct
    suffices h_step_decrease : ∀ t, V (t + 1) ≤ V t by
      exact antitone_nat_of_succ_le h_step_decrease hst
    intro t
    by_cases hVt : V t = 0
    · -- If V(t) = 0, then V(t+1) = 0 ≤ 0 = V(t)
      have hV_next : V (t + 1) = 0 := by
        change lyapunovV (M (t + 1)) v hn = 0
        rw [h_step t]
        exact lyapunovV_zero_preserved φ br (w t) q (M t) hn v (hv t) (hw_pos t v) hVt
      linarith [hV_nonneg (t + 1)]
    · -- If V(t) > 0, use lyapunov_strict_decrease
      have hVt_pos : 0 < V t := lt_of_le_of_ne (hV_nonneg t) (Ne.symm hVt)
      change lyapunovV (M (t + 1)) v hn ≤ lyapunovV (M t) v hn
      rw [h_step t]
      exact le_of_lt (lyapunov_strict_decrease φ br (w t) q (M t) hn v
        (hv t) (hv_unique t) (hw_pos t) hVt_pos)
  -- Step 3: V is bounded below, so it converges to its infimum
  have hV_bdd : BddBelow (Set.range V) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact hV_nonneg t⟩
  have hV_tendsto : Filter.Tendsto V Filter.atTop (nhds (⨅ t, V t)) :=
    tendsto_atTop_ciInf hV_antitone hV_bdd
  -- Step 4: Show the infimum is 0
  -- The infimum L satisfies L ≥ 0 (since all V(t) ≥ 0)
  have hL_nonneg : 0 ≤ ⨅ t, V t := le_ciInf (fun t => hV_nonneg t)
  -- If L > 0, then for all t, V(t) ≥ L > 0, so lyapunov_strict_decrease
  -- gives V(t+1) < V(t), meaning V is *strictly* decreasing.
  -- But V converges to L, so for any ε > 0, |V(t) - L| < ε for large t.
  -- In particular V(t) < L + ε and V(t+1) < V(t),
  -- so the sequence is Cauchy in [L, L+ε].
  -- The strict decrease at every step means V(t) - V(t+1) > 0 for all t,
  -- but ∑ (V(t) - V(t+1)) = V(0) - L < ∞, so V(t) - V(t+1) → 0.
  -- This requires showing the contraction rate γ(t) → 0 at the limit,
  -- which contradicts compactness (the limit point would have γ > 0).
  --
  -- This argument uses:
  -- (a) Contraction rate bound (contraction_rate_bound)
  -- (b) Compactness of bounded sequences (BolzanoWeierstrass)
  -- (c) Continuity of the contraction rate map
  suffices hL_zero : ⨅ t, V t = 0 by
    rw [hL_zero] at hV_tendsto; exact hV_tendsto
  -- Proof that infimum = 0 by contradiction
  by_contra hL_ne
  have hL_pos : 0 < ⨅ t, V t := lt_of_le_of_ne hL_nonneg (Ne.symm hL_ne)
  -- Every V(t) > 0, so strict decrease holds at every step
  have hV_pos : ∀ t, 0 < V t := by
    intro t
    exact lt_of_lt_of_le hL_pos (ciInf_le ⟨0, by rintro _ ⟨s, rfl⟩; exact hV_nonneg s⟩ t)
  -- V is strictly decreasing: V(t+1) < V(t) for all t
  have hV_strict : ∀ t, V (t + 1) < V t := by
    intro t
    change lyapunovV (M (t + 1)) v hn < lyapunovV (M t) v hn
    rw [h_step t]
    exact lyapunov_strict_decrease φ br (w t) q (M t) hn v
      (hv t) (hv_unique t) (hw_pos t) (hV_pos t)
  -- Step 5: Use contraction_rate_uniform_lower_bound to get γ₀ > 0
  -- such that γ(t) ≥ γ₀ for all t (by compactness of bounded M with weight gap).
  set L := ⨅ t, V t with L_def
  have hV_ge_L : ∀ t, L ≤ V t :=
    fun t => ciInf_le ⟨0, by rintro _ ⟨s, rfl⟩; exact hV_nonneg s⟩ t
  obtain ⟨γ₀, hγ₀_pos, hγ₀_le_one, hγ₀_le⟩ :=
    contraction_rate_uniform_lower_bound φ br q hn v M w hv hv_unique
      hw_pos h_bounded h_weight_gap
  -- Step 6: contraction_rate_bound gives V(t+1) ≤ (1 - γ(t)) * V(t)
  have hV_contract : ∀ t, V (t + 1) ≤ (1 - γ₀) * V t := by
    intro t
    -- Apply contraction_rate_bound at time t
    have h_crb := contraction_rate_bound φ br (w t) q (M t) hn v
      (hv t) (hv_unique t) (hw_pos t)
    -- h_crb introduces let-bindings; simplify them
    simp only [] at h_crb
    calc V (t + 1)
        = lyapunovV (M (t + 1)) v hn := rfl
      _ = lyapunovV (consolidationStep φ br (w t) q (M t) (by omega))
            v hn := by rw [h_step t]
      _ ≤ (1 - contractionRate φ br (w t) q (M t) v hn) *
            lyapunovV (M t) v hn := h_crb
      _ ≤ (1 - γ₀) * V t := by
          apply mul_le_mul_of_nonneg_right _ (hV_nonneg t)
          linarith [hγ₀_le t]
  -- Step 7: Geometric convergence forces V → 0
  have hc_nonneg : 0 ≤ 1 - γ₀ := by linarith [hγ₀_le_one]
  have hc_lt : 1 - γ₀ < 1 := by linarith [hγ₀_pos]
  have hV_to_zero : Filter.Tendsto V Filter.atTop (nhds 0) :=
    geometric_tendsto_zero V (1 - γ₀) hc_nonneg hc_lt hV_nonneg hV_contract
  -- Step 8: Contradiction — V → 0 but V(t) ≥ L > 0
  have : ∀ᶠ t in Filter.atTop, V t < L := by
    apply (Filter.Tendsto.eventually_lt hV_to_zero
      tendsto_const_nhds hL_pos).mono
    intro t ht; exact ht
  obtain ⟨t₀, ht₀⟩ := this.exists
  linarith [hV_ge_L t₀]

/-- Auxiliary: each ‖M i - M v‖ ≤ lyapunovV for i ≠ v, and = 0 for i = v. -/
private theorem norm_sub_anchor_le
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v i : Fin n) (hn : 2 ≤ n) :
    ‖M i - M v‖ ≤ lyapunovV M v hn := by
  by_cases hiv : i = v
  · rw [hiv, sub_self, norm_zero]; exact lyapunovV_nonneg M v hn
  · exact Finset.le_sup' (fun j => ‖M j - M v‖)
      (Finset.mem_erase.mpr ⟨hiv, Finset.mem_univ i⟩)

-- Auxiliary: diameter ≤ 2 * lyapunovV.
-- By triangle inequality: ‖M_i - M_j‖ ≤ ‖M_i - M_v‖ + ‖M_v - M_j‖ ≤ 2V.
set_option maxHeartbeats 400000 in
-- needed for Finset.sup' unfolding over product types
theorem diameter_le_two_lyapunovV
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) :
    diameter M (by omega) ≤ 2 * lyapunovV M v hn := by
  unfold diameter
  apply Finset.sup'_le
  intro p hp
  set V := lyapunovV M v hn
  have hi : ‖M p.1 - M v‖ ≤ V := norm_sub_anchor_le M v p.1 hn
  have hj : ‖M v - M p.2‖ ≤ V := by
    rw [norm_sub_rev]; exact norm_sub_anchor_le M v p.2 hn
  calc ‖M p.1 - M p.2‖
      = ‖(M p.1 - M v) + (M v - M p.2)‖ := by congr 1; abel
    _ ≤ ‖M p.1 - M v‖ + ‖M v - M p.2‖ := norm_add_le _ _
    _ ≤ V + V := add_le_add hi hj
    _ = 2 * V := by ring

-- diameter ≥ 0: follows from lyapunovV ≤ diameter bound and lyapunovV ≥ 0.
-- We actually just need diameter ≤ 2*V and 0 ≤ V, so diameter ≥ 0 follows
-- from a direct argument: V ≤ diameter (any ‖M j - M v‖ ≤ diameter since (j,v) is a pair).
-- To avoid expensive unfolding, we use lyapunovV_le_diameter below.
set_option maxHeartbeats 4000000 in
-- needed for Finset.sup' unfolding over product types in diameter definition
theorem lyapunovV_le_diameter
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) :
    lyapunovV M v hn ≤ diameter M (by omega) := by
  simp only [lyapunovV, diameter]
  apply Finset.sup'_le
  intro j hj
  exact Finset.le_sup' (fun (p : Fin n × Fin n) => ‖M p.1 - M p.2‖)
    (Finset.mk_mem_product (Finset.mem_univ j) (Finset.mem_univ v))

/-- cor:sleep (diameter version): D(t) → 0 as well. -/
theorem diameter_converges_to_zero
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
    (h_step : ∀ t, M (t + 1) = consolidationStep φ br (w t) q (M t) (by omega))
    (h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R)
    (h_weight_gap : ∃ δ : ℝ, 0 < δ ∧ ∀ t k, k ≠ v → w t k ≤ (1 - δ) * w t v) :
    Filter.Tendsto (fun t => diameter (M t) (by omega)) Filter.atTop (nhds 0) := by
  -- Squeeze theorem: 0 ≤ diameter(M t) ≤ 2 * V(t) and V(t) → 0
  have hV_tendsto : Filter.Tendsto (fun t => lyapunovV (M t) v hn) Filter.atTop (nhds 0) :=
    convergence_under_consolidation φ br q hn v M w hv hv_unique hw_pos h_step h_bounded
      h_weight_gap
  apply squeeze_zero
  · intro t
    exact le_trans (lyapunovV_nonneg (M t) v hn) (lyapunovV_le_diameter (M t) v hn)
  · intro t; exact diameter_le_two_lyapunovV (M t) v hn
  · -- 2 * V(t) → 0
    have : Filter.Tendsto (fun t => (2 : ℝ) * lyapunovV (M t) v hn)
        Filter.atTop (nhds ((2 : ℝ) * 0)) :=
      hV_tendsto.const_mul 2
    simp only [mul_zero] at this
    exact this
