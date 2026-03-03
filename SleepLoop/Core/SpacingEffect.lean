/-
  SleepLoop/Core/SpacingEffect.lean

  Spacing Effect: massed vs spaced accumulation, inverted-U, optimal spacing.

  Results:
  1. Massed bound: C_n^2 >= C_0^2 + delta * n * (n+1)
  2. Spaced bound: C_{n*K}^2 >= C_0^2 + 2 * delta * n
  3. Inverted-U: f(K) = sqrt(K)/((n-1)*K+R) has unique max at K* = R/(n-1)
  4. Optimal spacing: K* = R/(n-1), so dK*/dR = 1/(n-1) > 0

  For the inverted-U (3), the proof is purely algebraic. The key insight is
  that f(K)^2 = K / (mK+R)^2 where m = n-1. Then f(K) <= f(K*) reduces to
  4*m*R*K <= (mK+R)^2, which follows from (mK-R)^2 >= 0.

  Paper: Proposition (prop:spacing), Corollary (cor:cepeda).
  Level: A.
-/
import SleepLoop.Defs.Accumulation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

/-! ## Massed Accumulation Bound -/

/-- One-step C-squared lower bound for the standard accumulation rule:
    C_{t+1} = C_t + a_t * (t+1) / C_t implies
    C_{t+1}^2 >= C_t^2 + 2 * a_t * (t+1).
    The extra squared remainder term (a_t*(t+1)/C_t)^2 is dropped. -/
private theorem C_sq_step_lower (Ct Cnext at_ : ℝ) (t : ℕ)
    (hC : 0 < Ct) (_ha : 0 ≤ at_)
    (hrec : Cnext = Ct + at_ * (↑t + 1) / Ct) :
    Cnext ^ 2 ≥ Ct ^ 2 + 2 * at_ * (↑t + 1) := by
  have hne : Ct ≠ 0 := ne_of_gt hC
  rw [hrec]
  nlinarith [sq_nonneg (at_ * (↑t + 1) / Ct),
             mul_div_cancel₀ (at_ * (↑t + 1)) hne]

/-- Massed accumulation bound: If n observations at intensity >= delta occur at
    consecutive times t=0,...,n-1, then C_n^2 >= C_0^2 + delta * n * (n+1).
    From telescoping: C_{t+1}^2 >= C_t^2 + 2*delta*(t+1),
    sum gives delta * sum_{t=0}^{n-1} 2*(t+1) = delta * n * (n+1).
    Paper: spacing effect (massed case). -/
theorem massed_accumulation_bound
    (C : ℕ → ℝ) (a : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hC_pos : ∀ t, 0 < C t)
    (ha_lb : ∀ t, δ ≤ a t)
    (h_rec : ∀ t, C (t + 1) = C t + a t * (↑t + 1) / C t) :
    ∀ n : ℕ, C n ^ 2 ≥ C 0 ^ 2 + δ * ↑n * (↑n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have h_step := C_sq_step_lower (C k) (C (k + 1)) (a k) k
      (hC_pos k) (le_trans (le_of_lt hδ) (ha_lb k)) (h_rec k)
    push_cast [Nat.cast_succ]
    nlinarith [ha_lb k]

/-! ## Spaced Accumulation Bound -/

/-- C is nondecreasing under the accumulation rule with nonneg attention. -/
private theorem C_nondec_of_nonneg_attention
    (C : ℕ → ℝ) (a : ℕ → ℝ)
    (hC_pos : ∀ t, 0 < C t) (ha_nn : ∀ t, 0 ≤ a t)
    (h_rec : ∀ t, C (t + 1) = C t + a t * (↑t + 1) / C t) :
    ∀ s t, s ≤ t → C s ≤ C t := by
  have hC_step : ∀ t, C t ≤ C (t + 1) := by
    intro t; rw [h_rec t]
    linarith [div_nonneg (mul_nonneg (ha_nn t) (by positivity : (0:ℝ) ≤ ↑t + 1))
              (le_of_lt (hC_pos t))]
  intro s t h; induction h with
  | refl => exact le_refl _
  | @step m _ ih => exact le_trans ih (hC_step m)

/-- Spaced accumulation bound: If n observations at intensity >= delta occur at
    times 0, K, 2K, ..., (n-1)K (with K >= 1), then
    C_{n*K}^2 >= C_0^2 + 2 * delta * n.

    Each observation at time i*K contributes at least 2*delta to C^2 (since
    the step gives >= 2*delta*(i*K+1) >= 2*delta). Summing gives the bound.

    Paper: spacing effect (spaced case). -/
theorem spaced_accumulation_lower
    (C : ℕ → ℝ) (a : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hC_pos : ∀ t, 0 < C t)
    (ha_nn : ∀ t, 0 ≤ a t)
    (h_rec : ∀ t, C (t + 1) = C t + a t * (↑t + 1) / C t)
    (n : ℕ) (K : ℕ) (hK : 1 ≤ K)
    (h_obs : ∀ i, i < n → δ ≤ a (i * K)) :
    C (n * K) ^ 2 ≥ C 0 ^ 2 + 2 * δ * ↑n := by
  have hC_mono := C_nondec_of_nonneg_attention C a hC_pos ha_nn h_rec
  -- Each observation at time i*K adds >= 2*delta to C^2
  have h_per_obs : ∀ i, i < n → C ((i + 1) * K) ^ 2 ≥ C (i * K) ^ 2 + 2 * δ := by
    intro i hi
    have h_step := C_sq_step_lower (C (i * K)) (C (i * K + 1)) (a (i * K)) (i * K)
      (hC_pos (i * K)) (le_trans (le_of_lt hδ) (h_obs i hi)) (h_rec (i * K))
    -- (i+1)*K >= i*K + 1 when K >= 1
    have h_time : i * K + 1 ≤ (i + 1) * K := by nlinarith
    have hm := hC_mono _ _ h_time
    have hCiK1 := hC_pos (i * K + 1)
    have hCi1K := hC_pos ((i + 1) * K)
    have h_sq : C (i * K + 1) ^ 2 ≤ C ((i + 1) * K) ^ 2 := by nlinarith [sq_nonneg (C ((i + 1) * K) - C (i * K + 1))]
    have hiK_nn : (0 : ℝ) ≤ (i * K : ℕ) := Nat.cast_nonneg _
    nlinarith [h_obs i hi]
  -- Telescope over n steps
  suffices h : ∀ k, k ≤ n → C (k * K) ^ 2 ≥ C 0 ^ 2 + 2 * δ * ↑k from
    h n (le_refl n)
  intro k
  induction k with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hobs := h_per_obs j (by omega)
    push_cast [Nat.cast_succ]
    nlinarith

/-! ## Inverted-U Optimality -/

section InvertedU

/-- The spacing-efficiency function f(K) = sqrt(K) / (m*K + R).
    Here m = n-1 is the number of inter-observation gaps.
    Paper: Proposition (prop:spacing). -/
noncomputable def spacingEfficiency (m R K : ℝ) : ℝ :=
  Real.sqrt K / (m * K + R)

/-- Core inequality for the inverted-U: 4*m*R*K <= (m*K + R)^2.
    Proof: (m*K + R)^2 - 4*m*R*K = (m*K - R)^2 >= 0.
    This encodes f(K)^2 <= f(K*)^2 = 1/(4*m*R).
    Paper: Proposition (prop:spacing). -/
theorem spacing_core_ineq (m R K : ℝ) :
    4 * m * R * K ≤ (m * K + R) ^ 2 := by
  nlinarith [sq_nonneg (m * K - R)]

/-- Strict version: when m*K != R, the inequality is strict. -/
theorem spacing_core_strict (m R K : ℝ) (hne : m * K ≠ R) :
    4 * m * R * K < (m * K + R) ^ 2 := by
  nlinarith [mul_self_pos.mpr (sub_ne_zero.mpr hne)]

/-- Helper: for nonneg reals, a^2 < b^2 implies a < b. -/
private theorem lt_of_sq_lt_sq {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (h : a ^ 2 < b ^ 2) : a < b := by
  nlinarith [sq_abs a, sq_abs b, abs_of_nonneg ha]

/-- The inverted-U has a unique maximum: for all K > 0 with K != R/m,
    f(K) < f(R/m). This is the main inverted-U theorem.

    Proof strategy: Compare f(K)^2 vs f(K*)^2 directly.
    f(K)^2 = K / (mK+R)^2  and  f(K*)^2 = (R/m) / (2R)^2 = 1/(4mR).
    The comparison 4mRK < (mK+R)^2 holds when mK != R, by (mK-R)^2 > 0.

    Paper: Proposition (prop:spacing), "the benefit curve is an inverted U". -/
theorem spacing_inverted_U_unique_max (m R K : ℝ)
    (hm : 0 < m) (hR : 0 < R) (hK : 0 < K) (hne : K ≠ R / m) :
    spacingEfficiency m R K < spacingEfficiency m R (R / m) := by
  unfold spacingEfficiency
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hRm : 0 < R / m := div_pos hR hm
  have hd : 0 < m * K + R := by positivity
  have hd_star_eq : m * (R / m) + R = 2 * R := by
    rw [mul_div_cancel₀ R hm_ne]; ring
  have hd_star : 0 < m * (R / m) + R := by rw [hd_star_eq]; positivity
  have hmKne : m * K ≠ R := by
    intro h; exact hne (by field_simp at h ⊢; linarith)
  have h_strict := spacing_core_strict m R K hmKne
  have f_nn : 0 ≤ Real.sqrt K / (m * K + R) :=
    div_nonneg (Real.sqrt_nonneg K) (le_of_lt hd)
  have f_star_nn : 0 ≤ Real.sqrt (R / m) / (m * (R / m) + R) :=
    div_nonneg (Real.sqrt_nonneg (R / m)) (le_of_lt hd_star)
  apply lt_of_sq_lt_sq f_nn f_star_nn
  rw [div_pow, Real.sq_sqrt (le_of_lt hK)]
  rw [div_pow, Real.sq_sqrt (le_of_lt hRm), hd_star_eq]
  -- Goal: K / (mK+R)^2 < (R/m) / (2*R)^2
  rw [div_lt_div_iff₀ (sq_pos_of_pos hd) (by positivity : (0:ℝ) < (2 * R) ^ 2)]
  -- Use nlinarith with the strict inequality: 4mRK < (mK+R)^2
  nlinarith [h_strict, sq_nonneg R, sq_nonneg m, mul_pos hm hR]

/-- The inverted-U is increasing below the optimum: if 0 < K1 < K2 <= K* = R/m,
    then f(K1) < f(K2).
    Proof via cross-multiplication and the algebraic identity
    K1*(mK2+R)^2 - K2*(mK1+R)^2 = (K2-K1)*(m^2*K1*K2 - R^2).
    Paper: Proposition (prop:spacing). -/
theorem spacing_increasing_below_optimum (m R K1 K2 : ℝ)
    (hm : 0 < m) (hR : 0 < R) (hK1 : 0 < K1) (hK1K2 : K1 < K2)
    (hK2 : K2 ≤ R / m) :
    spacingEfficiency m R K1 < spacingEfficiency m R K2 := by
  unfold spacingEfficiency
  have hK2_pos : 0 < K2 := lt_trans hK1 hK1K2
  have hd1 : 0 < m * K1 + R := by positivity
  have hd2 : 0 < m * K2 + R := by positivity
  rw [div_lt_div_iff₀ hd1 hd2]
  have lhs_nn : 0 ≤ Real.sqrt K1 * (m * K2 + R) := by positivity
  have rhs_nn : 0 ≤ Real.sqrt K2 * (m * K1 + R) := by positivity
  apply lt_of_sq_lt_sq lhs_nn rhs_nn
  rw [mul_pow, Real.sq_sqrt (le_of_lt hK1)]
  rw [mul_pow, Real.sq_sqrt (le_of_lt hK2_pos)]
  -- Goal: K1 * (m*K2+R)^2 < K2 * (m*K1+R)^2
  -- Identity: K1*(mK2+R)^2 - K2*(mK1+R)^2 = (K2-K1)*(m^2*K1*K2 - R^2)
  -- Since K1 < K2 <= R/m: K1*K2 < (R/m)^2, so m^2*K1*K2 < R^2
  have hK1K2_prod : K1 * K2 < (R / m) ^ 2 := by
    calc K1 * K2 < K2 * K2 := by nlinarith
      _ ≤ (R / m) ^ 2 := by nlinarith [sq_nonneg (R / m - K2)]
  -- m^2 * K1 * K2 < R^2
  have h_m2K : m ^ 2 * (K1 * K2) < R ^ 2 := by
    have hm2 : (0:ℝ) < m ^ 2 := sq_pos_of_pos hm
    have : (R / m) ^ 2 * m ^ 2 = R ^ 2 := by field_simp
    nlinarith
  -- Use the factorization directly via nlinarith
  nlinarith

/-- The inverted-U is decreasing above the optimum: if K* = R/m <= K1 < K2,
    then f(K1) > f(K2).
    Paper: Proposition (prop:spacing). -/
theorem spacing_decreasing_above_optimum (m R K1 K2 : ℝ)
    (hm : 0 < m) (hR : 0 < R) (hK1 : R / m ≤ K1) (hK1K2 : K1 < K2) :
    spacingEfficiency m R K2 < spacingEfficiency m R K1 := by
  unfold spacingEfficiency
  have hRm : 0 < R / m := div_pos hR hm
  have hK1_pos : 0 < K1 := lt_of_lt_of_le hRm hK1
  have hK2_pos : 0 < K2 := lt_trans hK1_pos hK1K2
  have hd1 : 0 < m * K1 + R := by positivity
  have hd2 : 0 < m * K2 + R := by positivity
  rw [div_lt_div_iff₀ hd2 hd1]
  have lhs_nn : 0 ≤ Real.sqrt K2 * (m * K1 + R) := by positivity
  have rhs_nn : 0 ≤ Real.sqrt K1 * (m * K2 + R) := by positivity
  apply lt_of_sq_lt_sq lhs_nn rhs_nn
  rw [mul_pow, Real.sq_sqrt (le_of_lt hK2_pos)]
  rw [mul_pow, Real.sq_sqrt (le_of_lt hK1_pos)]
  -- Goal: K2 * (m*K1+R)^2 < K1 * (m*K2+R)^2
  -- From: K1*K2 > (R/m)^2, so m^2*K1*K2 > R^2
  have hK1K2_prod : K1 * K2 > (R / m) ^ 2 := by
    calc K1 * K2 > K1 * K1 := by nlinarith
      _ ≥ (R / m) ^ 2 := by nlinarith [sq_nonneg (K1 - R / m)]
  have h_m2K : m ^ 2 * (K1 * K2) > R ^ 2 := by
    have hm2 : (0:ℝ) < m ^ 2 := sq_pos_of_pos hm
    have : (R / m) ^ 2 * m ^ 2 = R ^ 2 := by field_simp
    nlinarith
  nlinarith

end InvertedU

/-! ## Optimal Spacing -/

section OptimalSpacing

/-- The optimal spacing formula: K* = R/m where m = n-1.
    Since m = n-1, this gives K* = R/(n-1).
    Paper: Corollary (cor:cepeda). -/
theorem optimal_spacing_formula (m R : ℝ) (hm : 0 < m) :
    m * (R / m) = R :=
  mul_div_cancel₀ R (ne_of_gt hm)

/-- Optimal spacing scales with retention: dK*/dR = 1/m > 0.
    This is immediate from K* = R/m: the mapping R -> R/m is linear
    with positive slope 1/m.
    Paper: Corollary (cor:cepeda), "optimal gap grows with retention interval". -/
theorem optimal_spacing_scales_with_retention (m R1 R2 : ℝ)
    (hm : 0 < m) (hR : R1 < R2) :
    R1 / m < R2 / m :=
  div_lt_div_of_pos_right hR hm

/-- At the optimal spacing, the squared efficiency equals 1/(4*m*R).
    This is the peak of the inverted-U curve. Working with the square avoids
    sqrt manipulation while capturing the same content.
    Paper: Proposition (prop:spacing). -/
theorem spacing_efficiency_sq_at_optimum (m R : ℝ) (hm : 0 < m) (hR : 0 < R) :
    spacingEfficiency m R (R / m) ^ 2 = 1 / (4 * m * R) := by
  unfold spacingEfficiency
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hRm : 0 < R / m := div_pos hR hm
  have hd_eq : m * (R / m) + R = 2 * R := by
    rw [mul_div_cancel₀ R hm_ne]; ring
  rw [div_pow, Real.sq_sqrt (le_of_lt hRm), hd_eq]
  -- Goal: (R/m) / (2*R)^2 = 1/(4*m*R)
  field_simp
  ring

end OptimalSpacing
