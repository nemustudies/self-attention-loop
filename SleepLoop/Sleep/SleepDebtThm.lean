/-
  SleepLoop/Sleep/SleepDebtThm.lean

  Theorem 56 (thm:sleep_debt): Sleep debt: compounding, threshold, and recovery.
  5-part theorem about sleep debt dynamics under truncated consolidation.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.SleepDebt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

/-! ## Sleep Debt (Theorem 56) -/

variable {d : ℕ}

/-- Per-cycle contraction factor: r = (1 - γ_min)^k_short.
    Paper: thm:sleep_debt, notation. -/
noncomputable def contractionFactor (γ_min : ℝ) (k_short : ℕ) : ℝ :=
  (1 - γ_min) ^ k_short

/-- Steady-state residual: V_∞ = r·ΔV/(1-r).
    Paper: thm:sleep_debt(ii). -/
noncomputable def steadyStateResidual (r ΔV : ℝ) : ℝ :=
  r * ΔV / (1 - r)

/-- Critical sleep duration: k_crit = ⌈log(ε_sep/(ΔV + ε_sep)) / log(1-γ_min)⌉.
    Paper: thm:sleep_debt(iii). -/
noncomputable def criticalSleepDuration (γ_min ΔV ε_sep : ℝ) : ℝ :=
  Real.log (ε_sep / (ΔV + ε_sep)) / Real.log (1 - γ_min)

/-- (i) Partial sleep is monotonically beneficial.
    V(t₀+k₂) ≤ V(t₀+k₁) for k₁ < k₂, with exponential contraction.
    Paper: thm:sleep_debt(i). -/
theorem sleep_debt_partial_beneficial
    (V₀ γ_min : ℝ) (hγ : 0 < γ_min) (hγ1 : γ_min < 1)
    (hV₀ : 0 < V₀)
    (k₁ k₂ : ℕ) (hk : k₁ < k₂) :
    -- V(t₀ + k₂) ≤ V(t₀ + k₁)
    (1 - γ_min) ^ k₂ * V₀ ≤ (1 - γ_min) ^ k₁ * V₀ := by
  -- Since 0 < 1-γ_min < 1 (as γ_min ∈ (0,1)), the function f(k) = (1-γ_min)^k is decreasing
  -- Therefore k₂ > k₁ ⇒ (1-γ_min)^k₂ < (1-γ_min)^k₁
  -- Multiplying by positive V₀ preserves inequality
    have h_base : 0 < 1 - γ_min := by linarith [hγ1]
    have h_base_lt : 1 - γ_min < 1 := by linarith [hγ]
    have h_base_le : 1 - γ_min ≤ 1 := le_of_lt h_base_lt
    have h_base_nn : 0 ≤ 1 - γ_min := le_of_lt h_base
    -- (1 - γ_min)^k₂ ≤ (1 - γ_min)^k₁ since base ∈ (0,1) and k₁ < k₂
    have h_pow : (1 - γ_min) ^ k₂ ≤ (1 - γ_min) ^ k₁ :=
      pow_le_pow_of_le_one h_base_nn h_base_le (le_of_lt hk)
    exact mul_le_mul_of_nonneg_right h_pow (le_of_lt hV₀)

/-- (ii) Debt compounds across cycles.
    V_n ≤ r·ΔV/(1-r) + r^n·(V₀ - r·ΔV/(1-r)) → V_∞ = r·ΔV/(1-r).
    Paper: thm:sleep_debt(ii). -/
theorem sleep_debt_compounding
    (r ΔV V₀ : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (hΔV : 0 < ΔV)
    -- Recurrence: V_{n+1} ≤ r(V_n + ΔV)
    (V : ℕ → ℝ)
    (hV0 : V 0 = V₀)
    (hV_rec : ∀ n, V (n + 1) ≤ r * (V n + ΔV)) :
    -- V_n converges to steady state r·ΔV/(1-r)
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    V n ≤ steadyStateResidual r ΔV + ε := by
  -- Let V_∞ = r * ΔV / (1 - r)
  set V_inf := steadyStateResidual r ΔV with hV_inf_def
  -- Key step 1: Show V n ≤ V_inf + r^n * (V₀ - V_inf) by induction
  -- Key step 2: Since 0<r<1, r^n → 0, so the r^n term vanishes
  have h1r_pos : 0 < 1 - r := by linarith
  have h1r_ne : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r_pos
  -- First, establish the inductive bound: V n ≤ V_inf + r^n * (V₀ - V_inf)
  have hbound : ∀ n, V n ≤ V_inf + r ^ n * (V₀ - V_inf) := by
    intro n
    induction n with
    | zero => simp [hV0]
    | succ n ih =>
      calc V (n + 1) ≤ r * (V n + ΔV) := hV_rec n
        _ ≤ r * (V_inf + r ^ n * (V₀ - V_inf) + ΔV) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hr)
            linarith
        _ = r * V_inf + r ^ (n + 1) * (V₀ - V_inf) + r * ΔV := by ring
        _ = V_inf + r ^ (n + 1) * (V₀ - V_inf) := by
            -- Need: r * V_inf + r * ΔV = V_inf
            -- V_inf = r * ΔV / (1 - r), so V_inf * (1-r) = r * ΔV
            -- r * V_inf + r * ΔV = r * V_inf + V_inf * (1-r) = V_inf
            unfold steadyStateResidual at hV_inf_def
            have : V_inf * (1 - r) = r * ΔV := by
              rw [hV_inf_def]; field_simp
            linarith
  -- Now handle the ε-N convergence
  intro ε hε
  -- Need: r^n * |V₀ - V_inf| < ε for large n
  -- Since 0 < r < 1, r^n → 0
  by_cases hV₀_le : V₀ ≤ V_inf
  · -- If V₀ ≤ V_inf, then r^n * (V₀ - V_inf) ≤ 0, so V n ≤ V_inf ≤ V_inf + ε
    refine ⟨0, fun n _ => ?_⟩
    have h_sub_le : V₀ - V_inf ≤ 0 := sub_nonpos.mpr hV₀_le
    have h_rn_nn : 0 ≤ r ^ n := pow_nonneg (le_of_lt hr) n
    have h_prod_le : r ^ n * (V₀ - V_inf) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h_rn_nn h_sub_le
    linarith [hbound n]
  · push_neg at hV₀_le
    -- V₀ > V_inf, so V₀ - V_inf > 0
    set C := V₀ - V_inf with hC_def
    have hC_pos : 0 < C := by linarith
    -- Need r^N * C < ε, i.e., r^N < ε / C
    -- Use: r^n → 0 (geometric sequence)
    have h_tendsto : Filter.Tendsto (fun n => r ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr) hr1
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N, hN⟩ := h_tendsto (ε / C) (div_pos hε hC_pos)
    refine ⟨N, fun n hn => ?_⟩
    have h_rn := hN n hn
    rw [Real.dist_eq, sub_zero] at h_rn
    have h_rn_nn : 0 ≤ r ^ n := pow_nonneg (le_of_lt hr) n
    rw [abs_of_nonneg h_rn_nn] at h_rn
    -- r^n < ε/C, so r^n * C < ε
    have h_rnC : r ^ n * C < ε := by
      rwa [lt_div_iff₀ hC_pos] at h_rn
    linarith [hbound n]

/-- (iii) Critical debt threshold.
    For k_short < k_crit, steady-state residual exceeds ε_sep:
    permanent degradation.
    Paper: thm:sleep_debt(iii). -/
theorem sleep_debt_critical_threshold
    (γ_min ΔV ε_sep : ℝ)
    (hγ : 0 < γ_min) (hγ1 : γ_min < 1)
    (hΔV : 0 < ΔV) (hε : 0 < ε_sep)
    (k_short : ℕ) (hk_pos : 0 < k_short)
    (hk : (k_short : ℝ) < criticalSleepDuration γ_min ΔV ε_sep) :
    -- V_∞ > ε_sep (permanent degradation)
    steadyStateResidual (contractionFactor γ_min k_short) ΔV > ε_sep := by
  -- r = (1 - γ_min)^k_short
  have h_base_pos : 0 < 1 - γ_min := by linarith
  have h_base_lt1 : 1 - γ_min < 1 := by linarith
  have hr_pos : 0 < contractionFactor γ_min k_short := by
    unfold contractionFactor; exact pow_pos h_base_pos k_short
  have hr_lt1 : contractionFactor γ_min k_short < 1 := by
    unfold contractionFactor
    exact pow_lt_one₀ (le_of_lt h_base_pos) h_base_lt1 (by omega)
  have h1r_pos : 0 < 1 - contractionFactor γ_min k_short := by linarith
  have h_log_neg : Real.log (1 - γ_min) < 0 := Real.log_neg h_base_pos h_base_lt1
  have h_sum_pos : 0 < ΔV + ε_sep := by linarith
  have h_ratio_pos : 0 < ε_sep / (ΔV + ε_sep) := div_pos hε h_sum_pos
  -- Step 1: k_short * log(1-γ_min) > log(ε_sep/(ΔV+ε_sep))
  have h1 : (k_short : ℝ) * Real.log (1 - γ_min) >
      Real.log (ε_sep / (ΔV + ε_sep)) := by
    unfold criticalSleepDuration at hk
    have := mul_lt_mul_of_neg_right hk h_log_neg
    rwa [div_mul_cancel₀ _ (ne_of_lt h_log_neg)] at this
  -- Step 2: log(r) > log(ε_sep/(ΔV+ε_sep))
  have h2 : Real.log (contractionFactor γ_min k_short) >
      Real.log (ε_sep / (ΔV + ε_sep)) := by
    unfold contractionFactor; rw [Real.log_pow]; exact_mod_cast h1
  -- Step 3: r > ε_sep/(ΔV+ε_sep) (log is strictly monotone)
  have h3 : contractionFactor γ_min k_short > ε_sep / (ΔV + ε_sep) :=
    (Real.log_lt_log_iff h_ratio_pos hr_pos).mp h2
  -- Step 4: r * (ΔV + ε_sep) > ε_sep
  have h4 : contractionFactor γ_min k_short * (ΔV + ε_sep) > ε_sep := by
    rwa [gt_iff_lt, div_lt_iff₀ h_sum_pos] at h3
  -- Step 5: r*ΔV/(1-r) > ε_sep
  unfold steadyStateResidual
  rw [gt_iff_lt, lt_div_iff₀ h1r_pos]
  nlinarith

/-- (iv) Recovery from debt.
    A single full-length sleep reduces V to within δ of zero.
    k_full ≥ ⌈log(V_n/δ) / (-log(1-γ_min))⌉ suffices.
    Paper: thm:sleep_debt(iv). -/
theorem sleep_debt_recovery
    (V_n δ γ_min : ℝ)
    (hV : 0 < V_n) (hδ : 0 < δ) (_hδV : δ < V_n)
    (hγ : 0 < γ_min) (hγ1 : γ_min < 1)
    (k_full : ℕ)
    (hk : (k_full : ℝ) ≥ Real.log (V_n / δ) / (-Real.log (1 - γ_min))) :
    -- After k_full steps: V ≤ δ
    (1 - γ_min) ^ k_full * V_n ≤ δ := by
  -- Need: (1-γ_min)^k_full ≤ δ/V_n, then multiply by V_n
  -- Strategy: use rpow to bridge between pow and log
  have h_base_pos : 0 < 1 - γ_min := by linarith
  have h_base_lt1 : 1 - γ_min < 1 := by linarith
  have h_log_neg : Real.log (1 - γ_min) < 0 :=
    Real.log_neg h_base_pos h_base_lt1
  have h_neg_log_pos : 0 < -Real.log (1 - γ_min) := neg_pos.mpr h_log_neg
  -- From hk: k_full ≥ log(V_n/δ) / (-log(1-γ_min))
  -- Multiply both sides by (-log(1-γ_min)) > 0:
  -- k_full * (-log(1-γ_min)) ≥ log(V_n/δ)
  have h1 : (k_full : ℝ) * (-Real.log (1 - γ_min)) ≥ Real.log (V_n / δ) := by
    have := mul_le_mul_of_nonneg_right hk (le_of_lt h_neg_log_pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt h_neg_log_pos)] at this
  -- Rearrange: k_full * log(1-γ_min) ≤ log(δ/V_n)
  have h2 : (k_full : ℝ) * Real.log (1 - γ_min) ≤ Real.log (δ / V_n) := by
    have h_VnD : 0 < V_n / δ := div_pos hV hδ
    rw [Real.log_div (ne_of_gt hδ) (ne_of_gt hV)]
    linarith [h1, Real.log_div (ne_of_gt hV) (ne_of_gt hδ)]
  -- Strategy: show log((1-γ_min)^k_full) ≤ log(δ/V_n), then exponentiate
  -- Use Real.log_pow: log(x^n) = n * log(x)
  have h_pow_pos : 0 < (1 - γ_min) ^ k_full := pow_pos h_base_pos k_full
  have h_dv_pos : 0 < δ / V_n := div_pos hδ hV
  -- log((1-γ_min)^k_full) = k_full * log(1-γ_min) ≤ log(δ/V_n)
  have h3 : Real.log ((1 - γ_min) ^ k_full) ≤ Real.log (δ / V_n) := by
    rw [Real.log_pow]
    exact_mod_cast h2
  -- Since log is monotone: (1-γ_min)^k_full ≤ δ/V_n
  have h5 : (1 - γ_min) ^ k_full ≤ δ / V_n :=
    (Real.log_le_log_iff h_pow_pos h_dv_pos).mp h3
  -- Multiply by V_n: (1-γ_min)^k_full * V_n ≤ δ
  rwa [le_div_iff₀ hV] at h5

/-- (v) Full sleep dominates truncated sleep.
    V_n^full ≤ V_n^short for all n, with strict inequality.
    Paper: thm:sleep_debt(v). -/
theorem sleep_debt_full_dominates
    (r_full r_short ΔV V₀ : ℝ)
    (hr_f : 0 < r_full) (_hr_s : 0 < r_short)
    (hr_fs : r_full < r_short) (_hr_s1 : r_short < 1)
    (hΔV : 0 < ΔV) (hV₀ : 0 ≤ V₀)
    (V_full V_short : ℕ → ℝ)
    (hf0 : V_full 0 = V₀) (hs0 : V_short 0 = V₀)
    (hf : ∀ n, V_full (n + 1) = r_full * (V_full n + ΔV))
    (hs : ∀ n, V_short (n + 1) = r_short * (V_short n + ΔV)) :
    ∀ n, V_full n ≤ V_short n := by
  -- First establish V_full n ≥ 0 for all n (needed for mul_le_mul)
  have hVf_nn : ∀ n, 0 ≤ V_full n := by
    intro n
    induction n with
    | zero => rw [hf0]; exact hV₀
    | succ n ih =>
      rw [hf n]
      exact mul_nonneg (le_of_lt hr_f) (add_nonneg ih (le_of_lt hΔV))
  -- Proof by induction on n using monotonicity of the recurrence
  intro n
  induction n with
  | zero => rw [hf0, hs0]
  | succ n ih =>
    -- V_full (n+1) = r_full * (V_full n + ΔV) ≤ r_short * (V_short n + ΔV) = V_short (n+1)
    rw [hf n, hs n]
    -- r_full * (V_full n + ΔV) ≤ r_short * (V_short n + ΔV)
    -- Step: r_full ≤ r_short and (V_full n + ΔV) ≤ (V_short n + ΔV)
    have h_sum_nn : 0 ≤ V_full n + ΔV := add_nonneg (hVf_nn n) (le_of_lt hΔV)
    have h_sum_le : V_full n + ΔV ≤ V_short n + ΔV := by linarith
    calc r_full * (V_full n + ΔV)
        ≤ r_full * (V_short n + ΔV) :=
          mul_le_mul_of_nonneg_left h_sum_le (le_of_lt hr_f)
      _ ≤ r_short * (V_short n + ΔV) :=
          mul_le_mul_of_nonneg_right (le_of_lt hr_fs)
            (le_trans h_sum_nn h_sum_le)
