/-
  SleepLoop/Sleep/RetrievalDegradation.lean

  Theorem 39 (thm:sleep_pressure): Retrieval degradation under sustained waking.
  5-part theorem about how retrieval precision degrades as |M| grows.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Retrieval Degradation (Theorem 39) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) Every capture event strictly decreases all existing retrieval weights.
    If M' = M ∪ {m_new}, then [softmax(qM'ᵀ)]_j < [softmax(qMᵀ)]_j for all j ∈ M.
    Paper: thm:sleep_pressure(i), the fan effect. -/
theorem sleep_pressure_fan_effect
    {n : ℕ} (hn : 0 < n)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (m_new : EuclideanSpace ℝ (Fin d))
    (j : Fin n) :
    -- The fan effect: adding a new impression strictly dilutes every existing
    -- retrieval weight.  We state this directly in terms of softmax scores:
    --   w_j = exp(s_j) / Σ_{k:Fin n} exp(s_k)
    --   w'_j = exp(s_j) / (exp(s_new) + Σ_{k:Fin n} exp(s_k))
    -- where s_k = q · m_k and s_new = q · m_new.
    let s : Fin n → ℝ := fun k => edot q (M k)
    let s_new : ℝ := edot q m_new
    Real.exp (s j) / (Real.exp s_new + ∑ k, Real.exp (s k)) <
      Real.exp (s j) / ∑ k, Real.exp (s k) := by
  -- Paper Thm 39(i): fan effect.
  -- The numerators are identical. The left denominator is strictly larger
  -- (by exp(s_new) > 0), so the left fraction is strictly smaller.
  simp only []
  haveI : NeZero n := ⟨by omega⟩
  set s := fun k : Fin n => edot q (M k)
  have h_denom_pos : 0 < ∑ k, Real.exp (s k) := softmax_denom_pos s
  have h_exp_new_pos : 0 < Real.exp (edot q m_new) := Real.exp_pos _
  have h_denom_lt : ∑ k, Real.exp (s k) < Real.exp (edot q m_new) + ∑ k, Real.exp (s k) :=
    lt_add_of_pos_left _ h_exp_new_pos
  exact div_lt_div_of_pos_left (Real.exp_pos (s j)) h_denom_pos h_denom_lt

/-- (ii) The score gap required for retrieval weight w_v ≥ c is g ≥ log((|M|-1)c/(1-c)).
    Paper: thm:sleep_pressure(ii). -/
theorem sleep_pressure_gap_requirement
    (n : ℕ) (hn : 1 < n)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (g : ℝ) (hg : g ≥ Real.log ((↑(n - 1) * c) / (1 - c))) :
    -- If score gap is g, the max softmax weight can achieve c
    1 / (1 + (↑(n - 1)) * Real.exp (-g)) ≥ c := by
  -- Paper Thm 39(ii): solve w_v ≥ 1/(1+(n-1)exp(-g)) ≥ c for g
  -- Equivalent to (n-1)exp(-g) ≤ (1-c)/c
  -- Taking logs: -g ≤ log((1-c)/c) = -log(c/(1-c))
  -- So g ≥ log((n-1)c/(1-c))
  have h_exp_positive : 0 < Real.exp g := Real.exp_pos g
  have h_ineq : (↑(n - 1) * c) / (1 - c) ≤ Real.exp g := by
    have h_log_le : Real.log ((↑(n - 1) * c) / (1 - c)) ≤ g := hg
    by_cases h_num_pos : (↑(n - 1) * c) / (1 - c) ≤ 0
    · exact le_trans h_num_pos (le_of_lt (Real.exp_pos g))
    · push_neg at h_num_pos
      rw [← Real.exp_log h_num_pos]
      exact Real.exp_le_exp.mpr h_log_le
  have n_pos : 0 < (↑(n - 1) : ℝ) := by
    exact Nat.cast_pos.mpr (by omega)
  have den_pos : 0 < 1 - c := by linarith [hc1]
  -- Goal: 1 / (1 + (n-1) * exp(-g)) ≥ c
  -- From h_ineq: (n-1)*c/(1-c) ≤ exp(g)
  -- Multiply both sides by (1-c)/c > 0: (n-1) ≤ exp(g) * (1-c)/c
  -- So (n-1) * exp(-g) ≤ (1-c)/c
  -- So 1 + (n-1)*exp(-g) ≤ 1 + (1-c)/c = 1/c
  -- So 1/(1 + (n-1)*exp(-g)) ≥ c
  have h_exp_neg_pos : 0 < Real.exp (-g) := Real.exp_pos _
  have h_denom_pos : 0 < 1 + ↑(n - 1) * Real.exp (-g) := by
    linarith [mul_nonneg (le_of_lt n_pos) (le_of_lt h_exp_neg_pos)]
  -- Suffices to show c * (1 + (n-1)*exp(-g)) ≤ 1
  rw [ge_iff_le, le_div_iff₀ h_denom_pos]
  -- Goal: c * (1 + (n-1) * exp(-g)) ≤ 1
  -- From h_ineq: (n-1)*c/(1-c) ≤ exp(g)
  -- So (n-1)*c ≤ exp(g) * (1-c)
  -- So (n-1)*c * exp(-g) ≤ (1-c)  [multiply by exp(-g)/1, since exp(-g) = 1/exp(g)]
  -- So c + (n-1)*c*exp(-g) ≤ c + (1-c) = 1
  -- i.e., c * (1 + (n-1)*exp(-g)) ≤ 1
  have h_step : ↑(n - 1) * c * Real.exp (-g) ≤ 1 - c := by
    have h1 : ↑(n - 1) * c ≤ Real.exp g * (1 - c) := by
      rw [div_le_iff₀ den_pos] at h_ineq; linarith
    have h2 : ↑(n - 1) * c / Real.exp g ≤ 1 - c := by
      rw [div_le_iff₀ (Real.exp_pos g)]; linarith
    calc ↑(n - 1) * c * Real.exp (-g)
        = ↑(n - 1) * c * (Real.exp g)⁻¹ := by rw [Real.exp_neg]
      _ = ↑(n - 1) * c / Real.exp g := by ring
      _ ≤ 1 - c := h2
  nlinarith
omit [DecidableEq X] in
/-- (iii) The achievable score gap is uniformly bounded: g ≤ 2R².
    Paper: thm:sleep_pressure(iii). -/
theorem sleep_pressure_gap_bound
    {n : ℕ} (hn : 2 ≤ n) -- scoreGap requires 2 ≤ n
    (E : Embedding X d)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hq : ‖q‖ ≤ E.R)
    (hM : ∀ j, ‖M j‖ ≤ E.R)
    (v : Fin n) :
    scoreGap q M v hn ≤ 2 * E.R ^ 2 := by
  -- Paper Thm 39(iii): g = q·m_v - max_{k≠v} q·m_k
  -- Use hull invariance: m_v, max_{k≠v}m_k ∈ conv(E(X)) ⊆ Ball(0,R)
  -- By Cauchy-Schwarz: q·m_v ≤ ‖q‖·‖m_v‖ ≤ R·R = R²
  -- Similarly max_{k≠v} q·m_k ≥ -‖q‖·‖m_k‖ ≥ -R² (worst case opposite direction)
  -- But more precisely, max is achieved at some k ≠ v within ball
  -- The maximum possible gap is when m_v and m_{k*} are opposite: g ≤ R² - (-R²) = 2R²
  unfold scoreGap
  -- g = edot q (M v) - sup'{k ≠ v} edot q (M k)
  -- edot q (M v) ≤ R² by Cauchy-Schwarz
  -- sup'{k ≠ v} edot q (M k) ≥ -R² since each edot q (M k) ≥ -R²
  -- Therefore g ≤ R² - (-R²) = 2R²
  have hR_nonneg : 0 ≤ E.R := le_of_lt E.radius_pos
  have h_upper : edot q (M v) ≤ E.R ^ 2 := by
    calc edot q (M v) ≤ |edot q (M v)| := le_abs_self _
      _ ≤ ‖q‖ * ‖M v‖ := abs_real_inner_le_norm q (M v)
      _ ≤ E.R * E.R := by apply mul_le_mul hq (hM v) (norm_nonneg _) hR_nonneg
      _ = E.R ^ 2 := by ring
  have h_nonempty := erase_v_nonempty hn v
  have h_lower : -(E.R ^ 2) ≤ Finset.sup' (Finset.univ.erase v) h_nonempty
      (fun k => (edot q (M k) : ℝ)) := by
    obtain ⟨k, hk⟩ := h_nonempty
    apply le_trans _ (Finset.le_sup' _ hk)
    -- Need: -(R^2) ≤ edot q (M k)
    -- We know |edot q (M k)| ≤ ‖q‖ * ‖M k‖ ≤ R * R = R^2
    -- So edot q (M k) ≥ -R^2
    have h_cs : |edot q (M k)| ≤ E.R ^ 2 := by
      calc |edot q (M k)| ≤ ‖q‖ * ‖M k‖ := abs_real_inner_le_norm q (M k)
        _ ≤ E.R * E.R := mul_le_mul hq (hM k) (norm_nonneg _) hR_nonneg
        _ = E.R ^ 2 := by ring
    linarith [neg_abs_le (edot q (M k))]
  linarith

/-- (iv) There exists a critical memory size |M*| = 1 + (1-c)/c · exp(2R²)
    beyond which no single impression can achieve retrieval weight ≥ c.
    Paper: thm:sleep_pressure(iv). -/
theorem sleep_pressure_critical_size
    (c R : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hR : 0 < R)
    (n : ℕ) (hn : (n : ℝ) > criticalMemorySize c R) :
    -- For any query, no impression achieves weight ≥ c
    ∀ (q : EuclideanSpace ℝ (Fin d))
      (M : Fin n → EuclideanSpace ℝ (Fin d))
      (_hq : ‖q‖ ≤ R) (_hM : ∀ j, ‖M j‖ ≤ R)
      (v : Fin n),
    retrievalWeights softmax q M v < c := by
  -- Paper Thm 39(iv): M* = 1 + (1-c)/c · exp(2R²)
  -- For n > M*, even with max score gap g = 2R², we have
  -- w_v = 1/(1+(n-1)exp(-g)) ≤ 1/(1+(M*-1)exp(-2R²)) = 1/(1+(1-c)/c) = c
  -- Strict inequality holds for n > M* (by gap monotonicity n → 1/(...))
  intro q M hq_bound hM_bound v
  -- Key bound: the softmax weight w_v = exp(s_v) / Σ exp(s_j)
  -- We show the denominator is large enough to force w_v < c.
  unfold retrievalWeights softmax
  simp only []
  -- Let s_j = edot q (M j)
  set s := fun j => edot q (M j) with hs_def
  -- The denominator sum is positive
  have hn_pos : 0 < n := by
    -- n > criticalMemorySize c R ≥ 1 > 0
    unfold criticalMemorySize at hn
    by_contra h; push_neg at h
    have : n = 0 := by omega
    subst this; simp at hn
    linarith [mul_nonneg (div_nonneg (le_of_lt (by linarith : 0 < 1 - c)) (le_of_lt hc0))
              (le_of_lt (Real.exp_pos (2 * R ^ 2)))]
  haveI : NeZero n := ⟨by omega⟩
  have h_denom_pos : 0 < ∑ j : Fin n, Real.exp (s j) := softmax_denom_pos s
  -- Want: exp(s v) / Σ_j exp(s j) < c
  -- Equivalently: exp(s v) < c * Σ_j exp(s j)
  rw [div_lt_iff₀ h_denom_pos]
  -- We lower-bound Σ_j exp(s j) by bounding each exp(s j) from below.
  -- Bound on each score: |s j| ≤ R² by Cauchy-Schwarz
  have hR_nn : 0 ≤ R := le_of_lt hR
  have h_score_bound : ∀ j, |s j| ≤ R ^ 2 := by
    intro j
    calc |s j| = |edot q (M j)| := rfl
      _ ≤ ‖q‖ * ‖M j‖ := abs_real_inner_le_norm q (M j)
      _ ≤ R * R := mul_le_mul hq_bound (hM_bound j) (norm_nonneg _) hR_nn
      _ = R ^ 2 := by ring
  -- So s j ≥ -(R²) and s v ≤ R² for all j
  have h_sv_upper : s v ≤ R ^ 2 := by linarith [le_abs_self (s v), h_score_bound v]
  have h_sj_lower : ∀ j, -(R ^ 2) ≤ s j := by
    intro j; linarith [neg_abs_le (s j), h_score_bound j]
  -- Therefore s j - s v ≥ -(2R²) for all j
  -- exp(s j) = exp(s v) * exp(s j - s v) ≥ exp(s v) * exp(-2R²)
  have h_exp_lower : ∀ j, Real.exp (s v) * Real.exp (-(2 * R ^ 2)) ≤ Real.exp (s j) := by
    intro j
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := h_sj_lower j
    linarith [h_sv_upper]
  -- Sum over all j: Σ_j exp(s j) ≥ n * exp(s v) * exp(-2R²)
  have h_sum_lower : ↑n * (Real.exp (s v) * Real.exp (-(2 * R ^ 2))) ≤
      ∑ j : Fin n, Real.exp (s j) := by
    have : ∑ j : Fin n, Real.exp (s v) * Real.exp (-(2 * R ^ 2)) ≤
        ∑ j : Fin n, Real.exp (s j) :=
      Finset.sum_le_sum (fun j _ => h_exp_lower j)
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  -- So c * Σ exp(s j) ≥ c * n * exp(s v) * exp(-2R²)
  -- We need exp(s v) < c * Σ exp(s j)
  -- Suffices: exp(s v) ≤ c * n * exp(s v) * exp(-2R²)
  -- i.e., 1 ≤ c * n * exp(-2R²)
  -- i.e., exp(2R²) ≤ c * n
  -- i.e., n ≥ exp(2R²)/c
  -- From hn: n > 1 + (1-c)/c * exp(2R²) = (c + (1-c)*exp(2R²))/c
  -- We need c * n * exp(-2R²) > 1
  -- From hn: n > 1 + (1-c)/c * exp(2R²)
  -- So c*n > c + (1-c) * exp(2R²)
  -- And c*n * exp(-2R²) > c*exp(-2R²) + (1-c)
  -- = 1 - c + c*exp(-2R²)
  -- This is > 1 iff c*exp(-2R²) > c, which holds only if exp(-2R²) > 1
  -- which is false for R > 0.
  -- So this simple bound doesn't work. Need to be more careful.
  -- Actually the correct approach: use that Σ_j exp(s j) ≥ exp(s v) + (n-1)*exp(s v - 2R²)
  -- = exp(s v) * (1 + (n-1)*exp(-2R²))
  -- So c * Σ ≥ c * exp(s v) * (1 + (n-1)*exp(-2R²))
  -- Need c * (1 + (n-1)*exp(-2R²)) > 1
  -- i.e. (n-1)*exp(-2R²) > (1-c)/c
  -- i.e. n-1 > (1-c)/c * exp(2R²)
  -- i.e. n > 1 + (1-c)/c * exp(2R²) = M*
  -- This follows from hn!
  -- Refine the bound: Σ ≥ exp(s v) * (1 + (n-1)*exp(-2R²))
  have h_sum_refined : Real.exp (s v) * (1 + ↑(n - 1) * Real.exp (-(2 * R ^ 2))) ≤
      ∑ j : Fin n, Real.exp (s j) := by
    -- Split sum into v and the rest
    have : ∑ j : Fin n, Real.exp (s j) =
        Real.exp (s v) + ∑ j ∈ Finset.univ.erase v, Real.exp (s j) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    rw [this]
    have h_rest : ↑(n - 1) * (Real.exp (s v) * Real.exp (-(2 * R ^ 2))) ≤
        ∑ j ∈ Finset.univ.erase v, Real.exp (s j) := by
      have h_card : (Finset.univ.erase v : Finset (Fin n)).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
      have h_each : ∀ j ∈ Finset.univ.erase v,
          Real.exp (s v) * Real.exp (-(2 * R ^ 2)) ≤ Real.exp (s j) :=
        fun j _ => h_exp_lower j
      calc ↑(n - 1) * (Real.exp (s v) * Real.exp (-(2 * R ^ 2)))
          = ∑ _j ∈ Finset.univ.erase v,
              Real.exp (s v) * Real.exp (-(2 * R ^ 2)) := by
            rw [Finset.sum_const, h_card, nsmul_eq_mul]
        _ ≤ ∑ j ∈ Finset.univ.erase v, Real.exp (s j) :=
            Finset.sum_le_sum h_each
    linarith [mul_comm (↑(n-1) : ℝ) (Real.exp (s v) * Real.exp (-(2 * R ^ 2))),
              Real.exp_pos (s v)]
  -- Now: c * Σ ≥ c * exp(s v) * (1 + (n-1)*exp(-2R²))
  -- Need: exp(s v) < c * Σ
  -- Suffices: c * (1 + (n-1)*exp(-2R²)) > 1
  suffices h_suff : 1 < c * (1 + ↑(n - 1) * Real.exp (-(2 * R ^ 2))) by
    calc Real.exp (s v)
        = Real.exp (s v) * 1 := (mul_one _).symm
      _ < Real.exp (s v) * (c * (1 + ↑(n - 1) * Real.exp (-(2 * R ^ 2)))) := by
          exact mul_lt_mul_of_pos_left h_suff (Real.exp_pos _)
      _ = c * (Real.exp (s v) * (1 + ↑(n - 1) * Real.exp (-(2 * R ^ 2)))) := by ring
      _ ≤ c * ∑ j : Fin n, Real.exp (s j) := by
          apply mul_le_mul_of_nonneg_left h_sum_refined (le_of_lt hc0)
  -- Need: c * (1 + (n-1)*exp(-2R²)) > 1
  -- i.e., (n-1)*exp(-2R²) > (1-c)/c
  -- i.e., n - 1 > (1-c)/c * exp(2R²)
  -- From hn: n > 1 + (1-c)/c * exp(2R²)
  -- So n - 1 > (1-c)/c * exp(2R²) (with care about Nat subtraction)
  unfold criticalMemorySize at hn
  have h_exp_2R2_pos : 0 < Real.exp (2 * R ^ 2) := Real.exp_pos _
  have h_exp_neg_pos : 0 < Real.exp (-(2 * R ^ 2)) := Real.exp_pos _
  have h_exp_neg_eq : Real.exp (-(2 * R ^ 2)) = (Real.exp (2 * R ^ 2))⁻¹ := Real.exp_neg _
  have h_n_minus_1 : ((n - 1 : ℕ) : ℝ) > (1 - c) / c * Real.exp (2 * R ^ 2) := by
    have h_1c_pos : (0 : ℝ) < 1 - c := by linarith
    have h_product_nn : (0 : ℝ) ≤ (1 - c) / c * Real.exp (2 * R ^ 2) :=
      mul_nonneg (div_nonneg (le_of_lt h_1c_pos) (le_of_lt hc0)) (le_of_lt h_exp_2R2_pos)
    have h_1_le_n : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have h_cast : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
    rw [h_cast]; linarith
  -- Now: (n-1) * exp(-2R²) > (1-c)/c * exp(2R²) * exp(-2R²) = (1-c)/c
  have h_prod : ↑(n - 1) * Real.exp (-(2 * R ^ 2)) > (1 - c) / c := by
    have h1 : (1 - c) / c * Real.exp (2 * R ^ 2) * Real.exp (-(2 * R ^ 2)) = (1 - c) / c := by
      rw [h_exp_neg_eq, mul_assoc, mul_inv_cancel₀ (ne_of_gt h_exp_2R2_pos), mul_one]
    linarith [mul_lt_mul_of_pos_right h_n_minus_1 h_exp_neg_pos]
  -- c * (1 + (n-1)*exp(-2R²)) > c * (1 + (1-c)/c) = c + (1-c) = 1
  calc (1 : ℝ) = c + (1 - c) := by ring
    _ = c * 1 + c * ((1 - c) / c) := by field_simp
    _ < c * 1 + c * (↑(n - 1) * Real.exp (-(2 * R ^ 2))) := by
        linarith [mul_lt_mul_of_pos_left h_prod hc0]
    _ = c * (1 + ↑(n - 1) * Real.exp (-(2 * R ^ 2))) := by ring

omit [DecidableEq X] in
/-- (v) Waking consolidation cannot prevent degradation:
    γ(t) → 0 as impressions equalize (self-limiting property).
    Paper: thm:sleep_pressure(v).

    The paper defines γ(t) = min_{j≠v} λ_j(1 - √(1 - α_v^{(j)})) where
    λ_j = 1 - w_j/w_v. As weights equalize (w_j/w_v → 1), λ_j → 0, so γ → 0.
    We capture this via the hypothesis `h_gamma_bound`: γ is bounded by a constant
    times the maximum weight ratio deviation. -/
theorem sleep_pressure_consolidation_futile
    {n : ℕ} (hn : 1 < n)
    (_E : Embedding X d)
    (_M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    -- As weights equalize, contraction rate vanishes
    (w : ℕ → Fin n → ℝ)
    (γ : ℕ → ℝ)
    (_h_gamma_nonneg : ∀ t, 0 ≤ γ t)
    -- Paper: γ(t) = min_{j≠v} λ_j · (bounded factor ∈ [0,1])
    --        λ_j = 1 - w_j/w_v ≤ |w_j/w_v - 1|
    -- So γ(t) ≤ max_{i,j} |w(t,i)/w(t,j) - 1| · 1 (geometric factor ≤ 1).
    -- We use constant C = 1 for the cleanest statement.
    (h_gamma_bound : ∀ t, γ t ≤ Finset.sup' (Finset.univ ×ˢ Finset.univ)
        (product_univ_nonempty (by omega : 0 < n))
        (fun p => |w t p.1 / w t p.2 - 1|))
    (h_equalize : ∀ ε > 0, ∃ T, ∀ t ≥ T, ∀ i j : Fin n,
      |w t i / w t j - 1| < ε) :
    -- γ(t) → 0
  ∀ ε > 0, ∃ T, ∀ t ≥ T, γ t < ε := by
  -- Paper Thm 39(v): γ(t) = min_{j≠v} λ_j(1 - √(1-α_v^j))
  -- As weights equalize: w_j/w_v → 1 ⇒ λ_j = 1 - w_j/w_v → 0
  -- By h_gamma_bound, γ t ≤ max_{i,j} |w_i/w_j - 1|
  -- By h_equalize, this max → 0, so γ → 0.
  intro ε hε
  obtain ⟨T, hT⟩ := h_equalize ε hε
  refine ⟨T, fun t ht => ?_⟩
  have h_sup_lt : Finset.sup' (Finset.univ ×ˢ Finset.univ)
      (product_univ_nonempty (by omega : 0 < n))
      (fun p => |w t p.1 / w t p.2 - 1|) < ε := by
    rw [Finset.sup'_lt_iff]
    intro p _hp
    exact hT t ht p.1 p.2
  linarith [h_gamma_bound t]
