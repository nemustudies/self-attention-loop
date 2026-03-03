/-
  SleepLoop/Rigidity/AccumulationRigidity.lean

  Proposition (prop:rigidity): Rigidity of the accumulation rate.
  Replace t+1 with an arbitrary scaling f(t) in the accumulation rule:
    C_{t+1} = C_t + a_t * f(t) / C_t.
  For sigma = C/N to converge to a nonzero finite constant under persistent
  observation (a >= delta > 0), f(t) ~ t is necessary.
  Level: A.
-/
import SleepLoop.Defs.Accumulation

open Finset BigOperators

/-! ## Accumulation Rigidity -/

/-- A generalized accumulation rule: C_{t+1} = C_t + a_t * f(t) / C_t
    where f : N -> R is a positive scaling function. -/
noncomputable def accumulateC_general
    {X : Type*} (C : X → ℝ) (a : X → ℝ) (f : ℕ → ℝ) (t : ℕ) (τ : X) : ℝ :=
  C τ + a τ * f t / C τ

/-! ### Helper: one-step squared increment -/

/-- One step of the squared recurrence: C(t+1)^2 = C(t)^2 + 2*a*f + (a*f/C)^2. -/
private theorem sq_step (C_val C_val' a_val f_val : ℝ) (hC : 0 < C_val)
    (hrec : C_val' = C_val + a_val * f_val / C_val) :
    C_val' ^ 2 = C_val ^ 2 + 2 * (a_val * f_val) + (a_val * f_val / C_val) ^ 2 := by
  rw [hrec]
  have hC_ne : C_val ≠ 0 := ne_of_gt hC
  have : C_val * (a_val * f_val / C_val) = a_val * f_val := mul_div_cancel₀ _ hC_ne
  have : (C_val + a_val * f_val / C_val) ^ 2 =
      C_val ^ 2 + 2 * (C_val * (a_val * f_val / C_val)) + (a_val * f_val / C_val) ^ 2 := by
    ring
  linarith

/-- Given the generalized accumulation rule C_{t+1} = C_t + a_t * f(t) / C_t
    with a_t >= delta > 0, we have C_t^2 >= C_0^2 + 2*delta * sum_{s<t} f(s).
    This is the key lower bound from the proof of prop:rigidity.
    Paper: prop:rigidity (lower bound step). -/
theorem accum_C_squared_lower_bound
    (C : ℕ → ℝ) (a : ℕ → ℝ) (f : ℕ → ℝ)
    (δ : ℝ) (_hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t) :
    ∀ t, C t ^ 2 ≥ C 0 ^ 2 + 2 * δ * ∑ s ∈ Finset.range t, f s := by
  intro t
  induction t with
  | zero =>
    simp [Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hCn_pos := hC_pos n
    have ha_n := ha_lb n
    have step : C (n + 1) ^ 2 ≥ C n ^ 2 + 2 * δ * f n := by
      rw [hC_rec n]
      set x := C n
      set y := a n * f n / C n
      have hx_ne : x ≠ 0 := ne_of_gt hCn_pos
      have hxy : x * y = a n * f n := by
        simp only [y]; rw [mul_div_cancel₀ _ hx_ne]
      have expand : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
      rw [expand, hxy]
      have : 0 ≤ y ^ 2 := sq_nonneg _
      have : δ * f n ≤ a n * f n :=
        mul_le_mul_of_nonneg_right ha_n (le_of_lt (hf_pos n))
      linarith
    linarith

/-! ### Squared upper bound -/

/-- Upper bound: C(t+1)^2 <= C(t)^2 + 3*f(t) when f(t) <= C(t)^2. -/
private theorem sq_upper_step_of_le (C_val C_next a_val f_val : ℝ)
    (hC : 0 < C_val) (ha_nn : 0 ≤ a_val) (ha_ub : a_val ≤ 1) (hf : 0 < f_val)
    (hfC : f_val ≤ C_val ^ 2)
    (hrec : C_next = C_val + a_val * f_val / C_val) :
    C_next ^ 2 ≤ C_val ^ 2 + 3 * f_val := by
  rw [hrec]
  have hC_ne : C_val ≠ 0 := ne_of_gt hC
  have hxy : C_val * (a_val * f_val / C_val) = a_val * f_val := mul_div_cancel₀ _ hC_ne
  have expand : (C_val + a_val * f_val / C_val) ^ 2 =
      C_val ^ 2 + 2 * (C_val * (a_val * f_val / C_val)) + (a_val * f_val / C_val) ^ 2 := by
    ring
  rw [expand, hxy]
  -- 2*(a*f) <= 2*f since a <= 1
  have h1 : a_val * f_val ≤ f_val := by nlinarith
  -- (a*f/C)^2 <= f^2/C^2 <= f (since f <= C^2)
  have h2 : (a_val * f_val / C_val) ^ 2 ≤ f_val := by
    rw [div_pow]
    have h_af_nn : 0 ≤ a_val * f_val := mul_nonneg ha_nn (le_of_lt hf)
    have : (a_val * f_val) ^ 2 ≤ f_val ^ 2 := by nlinarith [sq_nonneg (f_val - a_val * f_val)]
    have hC2_pos : (0 : ℝ) < C_val ^ 2 := by positivity
    calc (a_val * f_val) ^ 2 / C_val ^ 2
        ≤ f_val ^ 2 / C_val ^ 2 := by
          apply div_le_div_of_nonneg_right
          · nlinarith
          · positivity
      _ ≤ f_val := by rw [div_le_iff₀ hC2_pos]; nlinarith
  linarith

/-! ### C is monotone and bounded below by C(0) -/

private theorem C_mono_of_rec (C a f : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (hC_pos : ∀ t, 0 < C t) (hf_pos : ∀ t, 0 < f t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t) :
    ∀ t, C t ≤ C (t + 1) := by
  intro t
  rw [hC_rec t]
  have : 0 < a t * f t / C t :=
    div_pos (mul_pos (by linarith [ha_lb t]) (hf_pos t)) (hC_pos t)
  linarith

private theorem C_ge_C0 (C a f : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (hC_pos : ∀ t, 0 < C t) (hf_pos : ∀ t, 0 < f t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t) :
    ∀ t, C 0 ≤ C t := by
  intro t
  induction t with
  | zero => exact le_refl _
  | succ n ih => exact le_trans ih (C_mono_of_rec C a f δ hδ ha_lb hC_pos hf_pos hC_rec n)

/-! ### Multi-step monotonicity -/

private theorem C_mono_le (C a f : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (hC_pos : ∀ t, 0 < C t) (hf_pos : ∀ t, 0 < f t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t) :
    ∀ s t, s ≤ t → C s ≤ C t := by
  intro s t h; induction h with
  | refl => exact le_refl _
  | @step m _ ih => exact le_trans ih (C_mono_of_rec C a f δ hδ ha_lb hC_pos hf_pos hC_rec m)

/-! ## Upper bound on Σf -/

/-- From C^2 >= 2*delta*Sigma_f and C <= 2*sigma_lim*D: Sigma_f <= (2*sigma_lim)^2/(2*delta)*D^2.
    Paper: prop:rigidity (upper bound on aggregate sum). -/
theorem sum_f_upper
    (C a f : ℕ → ℝ) (N₀ : ℕ) (_hN₀ : 0 < N₀)
    (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t)
    (σ_lim : ℝ) (hσ_pos : 0 < σ_lim)
    (hσ_conv : ∀ ε > 0, ∃ T, ∀ t ≥ T, |C t / (↑N₀ + ↑t) - σ_lim| ≤ ε) :
    ∃ T, ∀ t ≥ T,
      ∑ s ∈ Finset.range t, f s ≤ (2 * σ_lim) ^ 2 / (2 * δ) * (↑N₀ + ↑t) ^ 2 := by
  obtain ⟨T₀, hT₀⟩ := hσ_conv σ_lim hσ_pos
  use T₀; intro t ht
  have hD_pos : (0 : ℝ) < ↑N₀ + ↑t := by positivity
  have hC_ub : C t ≤ 2 * σ_lim * (↑N₀ + ↑t) := by
    have hb := hT₀ t ht; rw [abs_le] at hb
    calc C t = C t / (↑N₀ + ↑t) * (↑N₀ + ↑t) := by
            rw [div_mul_cancel₀ _ (ne_of_gt hD_pos)]
      _ ≤ (σ_lim + σ_lim) * (↑N₀ + ↑t) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hD_pos); linarith [hb.2]
      _ = 2 * σ_lim * (↑N₀ + ↑t) := by ring
  have h_sq := accum_C_squared_lower_bound C a f δ hδ ha_lb hC_pos hC_rec hf_pos t
  have hC2_ub : C t ^ 2 ≤ (2 * σ_lim * (↑N₀ + ↑t)) ^ 2 :=
    sq_le_sq' (by nlinarith [hC_pos t]) hC_ub
  have h2δ_pos : (0 : ℝ) < 2 * δ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h2δ_pos]
  nlinarith [sq_nonneg (C 0)]

/-! ## Eventually f ≤ C² (from σ convergence) -/

set_option maxHeartbeats 400000 in
-- needed for complex epsilon-delta computation with many nlinarith calls
/-- Eventually f(t) <= C(t)^2.
    From the recurrence, a*f = C*(C(t+1) - C(t)), so f <= C*Delta/delta.
    Using sigma-convergence, Delta = O(1 + eps*D) and C = O(sigma*D),
    so f = O(sigma*D*(1+eps*D)/delta).
    But C^2 >= (sigma-eps)^2*D^2. Choosing eps = sigma*delta/10 makes the D^2 coeff
    of f strictly smaller than (sigma-eps)^2, so f <= C^2 for D large.
    Paper: prop:rigidity (epsilon-delta step). -/
theorem eventually_f_le_C_sq
    (C a f : ℕ → ℝ) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t) (hf_pos : ∀ t, 0 < f t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (σ_lim : ℝ) (hσ_pos : 0 < σ_lim)
    (hσ_conv : ∀ ε > 0, ∃ T, ∀ t ≥ T, |C t / (↑N₀ + ↑t) - σ_lim| ≤ ε) :
    ∃ T, ∀ t ≥ T, f t ≤ C t ^ 2 := by
  have hδ_le : δ ≤ 1 := le_trans (ha_lb 0) (ha_ub 0)
  set ε := σ_lim * δ / 10 with hε_def
  have hε_pos : (0 : ℝ) < ε := by positivity
  have hσε_pos : (0 : ℝ) < σ_lim - ε := by rw [hε_def]; nlinarith
  obtain ⟨T₀, hT₀⟩ := hσ_conv ε hε_pos
  have hgap : (σ_lim - ε) ^ 2 * δ > 2 * ε * (σ_lim + ε) := by
    rw [hε_def]
    have h1 : δ ^ 2 - 22 * δ + 80 > 0 := by nlinarith [sq_nonneg (1 - δ)]
    nlinarith [sq_nonneg σ_lim, sq_nonneg δ, sq_nonneg (σ_lim * δ)]
  set gap := (σ_lim - ε) ^ 2 - 2 * ε * (σ_lim + ε) / δ with hgap_def
  have hgap_pos : (0 : ℝ) < gap := by
    rw [hgap_def, sub_pos, div_lt_iff₀ hδ]; linarith
  obtain ⟨D₀, hD₀⟩ := exists_nat_gt ((σ_lim + ε) ^ 2 / (δ * gap))
  use max T₀ D₀
  intro t ht
  have ht_T₀ : t ≥ T₀ := le_trans (le_max_left _ _) ht
  have ht_D₀ : t ≥ D₀ := le_trans (le_max_right _ _) ht
  set D := (↑N₀ : ℝ) + (↑t : ℝ) with hD_def
  have hD_pos : (0 : ℝ) < D := by positivity
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hD_ge : D ≥ ↑D₀ := by
    have h1 : (↑D₀ : ℝ) ≤ (↑t : ℝ) := Nat.cast_le.mpr ht_D₀
    have h2 : (0 : ℝ) ≤ (↑N₀ : ℝ) := Nat.cast_nonneg N₀
    linarith
  have hσ_t := hT₀ t ht_T₀
  rw [abs_le] at hσ_t
  have hC_lb : (σ_lim - ε) * D ≤ C t := by
    calc (σ_lim - ε) * D ≤ C t / D * D := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hD_pos); linarith [hσ_t.1]
      _ = C t := div_mul_cancel₀ _ hD_ne
  have hC_ub : C t ≤ (σ_lim + ε) * D := by
    calc C t = C t / D * D := (div_mul_cancel₀ _ hD_ne).symm
      _ ≤ (σ_lim + ε) * D := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hD_pos); linarith [hσ_t.2]
  have hσ_t1 := hT₀ (t + 1) (by omega)
  rw [abs_le] at hσ_t1
  have hD1_pos : (0 : ℝ) < D + 1 := by linarith
  have hC1_ub : C (t + 1) ≤ (σ_lim + ε) * (D + 1) := by
    have hD1_eq : (↑N₀ : ℝ) + (↑(t + 1) : ℝ) = D + 1 := by push_cast; ring
    calc C (t + 1) = C (t + 1) / (D + 1) * (D + 1) := by
            rw [div_mul_cancel₀ _ (ne_of_gt hD1_pos)]
      _ ≤ (σ_lim + ε) * (D + 1) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hD1_pos)
            rw [← hD1_eq]; linarith [hσ_t1.2]
  have hΔ_nn : 0 ≤ C (t + 1) - C t := by
    have := C_mono_le C a f δ hδ ha_lb hC_pos hf_pos hC_rec t (t + 1) (by omega)
    linarith
  have hΔ_ub : C (t + 1) - C t ≤ (σ_lim + ε) + 2 * ε * D := by
    calc C (t + 1) - C t
        ≤ (σ_lim + ε) * (D + 1) - (σ_lim - ε) * D := by linarith
      _ = (σ_lim + ε) + 2 * ε * D := by ring
  have hf_eq : a t * f t = C t * (C (t + 1) - C t) := by
    have hrec := hC_rec t
    have hC_ne : C t ≠ 0 := ne_of_gt (hC_pos t)
    have h1 : C (t + 1) - C t = a t * f t / C t := by linarith
    rw [h1, mul_div_cancel₀ _ hC_ne]
  have hf_ub : f t ≤ C t * (C (t + 1) - C t) / δ := by
    rw [le_div_iff₀ hδ]
    calc f t * δ ≤ f t * a t := by nlinarith [ha_lb t, hf_pos t]
      _ = a t * f t := by ring
      _ = C t * (C (t + 1) - C t) := hf_eq
  have hf_ub2 : f t ≤ (σ_lim + ε) * D * ((σ_lim + ε) + 2 * ε * D) / δ := by
    apply le_trans hf_ub
    apply div_le_div_of_nonneg_right _ (le_of_lt hδ)
    apply mul_le_mul hC_ub hΔ_ub hΔ_nn (by positivity)
  have hC_sq_lb : (σ_lim - ε) ^ 2 * D ^ 2 ≤ C t ^ 2 := by
    calc (σ_lim - ε) ^ 2 * D ^ 2
        = ((σ_lim - ε) * D) ^ 2 := by ring
      _ ≤ C t ^ 2 := sq_le_sq' (by nlinarith [hC_pos t]) hC_lb
  have key : (σ_lim + ε) * D * ((σ_lim + ε) + 2 * ε * D) ≤
      (σ_lim - ε) ^ 2 * D ^ 2 * δ := by
    have hDδgap : (σ_lim + ε) ^ 2 < D * (δ * gap) := by
      have h1 : (σ_lim + ε) ^ 2 / (δ * gap) < (↑D₀ : ℝ) := hD₀
      have h2 : (↑D₀ : ℝ) ≤ D := hD_ge
      calc (σ_lim + ε) ^ 2
          < (↑D₀ : ℝ) * (δ * gap) := by
            rwa [div_lt_iff₀ (mul_pos hδ hgap_pos)] at h1
        _ ≤ D * (δ * gap) := by
            apply mul_le_mul_of_nonneg_right h2 (le_of_lt (mul_pos hδ hgap_pos))
    have hδgap : δ * gap = δ * (σ_lim - ε) ^ 2 - 2 * ε * (σ_lim + ε) := by
      rw [hgap_def, mul_sub, mul_div_cancel₀ _ (ne_of_gt hδ)]
    rw [hδgap] at hDδgap
    have hDδgap' : D * (σ_lim + ε) ^ 2 < D ^ 2 * (δ * (σ_lim - ε) ^ 2 - 2 * ε * (σ_lim + ε)) := by
      calc D * (σ_lim + ε) ^ 2
          < D * (D * (δ * (σ_lim - ε) ^ 2 - 2 * ε * (σ_lim + ε))) := by
            apply mul_lt_mul_of_pos_left hDδgap hD_pos
        _ = D ^ 2 * (δ * (σ_lim - ε) ^ 2 - 2 * ε * (σ_lim + ε)) := by ring
    have lhs_expand : (σ_lim + ε) * D * ((σ_lim + ε) + 2 * ε * D) =
        (σ_lim + ε) ^ 2 * D + 2 * ε * (σ_lim + ε) * D ^ 2 := by ring
    have rhs_expand : (σ_lim - ε) ^ 2 * D ^ 2 * δ =
        D ^ 2 * (δ * (σ_lim - ε) ^ 2 - 2 * ε * (σ_lim + ε)) +
        2 * ε * (σ_lim + ε) * D ^ 2 := by ring
    rw [lhs_expand, rhs_expand]
    linarith
  calc f t
      ≤ (σ_lim + ε) * D * ((σ_lim + ε) + 2 * ε * D) / δ := hf_ub2
    _ ≤ (σ_lim - ε) ^ 2 * D ^ 2 := by rw [div_le_iff₀ hδ]; linarith
    _ ≤ C t ^ 2 := hC_sq_lb

/-! ## Telescoped upper bound on C² -/

/-- If f ≤ C² eventually, then C(T₀+t)² ≤ C(T₀)² + 3·Σf. -/
private theorem C_sq_upper_telescope
    (C a f : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t) (hf_pos : ∀ t, 0 < f t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (T₀ : ℕ) (hfC : ∀ t, T₀ ≤ t → f t ≤ C t ^ 2) :
    ∀ t, C (T₀ + t) ^ 2 ≤ C T₀ ^ 2 + 3 * ∑ s ∈ Finset.range t, f (T₀ + s) := by
  intro t; induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have ha_nn : 0 ≤ a (T₀ + n) := le_trans (le_of_lt hδ) (ha_lb (T₀ + n))
    have hrec_eq : C (T₀ + n + 1) = C (T₀ + n) + a (T₀ + n) * f (T₀ + n) / C (T₀ + n) := by
      have h := hC_rec (T₀ + n); convert h using 1
    have key : C (T₀ + n + 1) ^ 2 ≤ C (T₀ + n) ^ 2 + 3 * f (T₀ + n) :=
      sq_upper_step_of_le (C (T₀ + n)) (C (T₀ + n + 1)) (a (T₀ + n)) (f (T₀ + n))
        (hC_pos (T₀ + n)) ha_nn (ha_ub (T₀ + n)) (hf_pos (T₀ + n))
        (hfC (T₀ + n) (Nat.le_add_right T₀ n)) hrec_eq
    have : T₀ + (n + 1) = T₀ + n + 1 := by omega
    rw [this]; linarith

/-! ## Lower bound on Σf -/

/-- Sigma_f >= alpha * D(t)^2 (eventually).
    Paper: prop:rigidity (lower bound on aggregate sum). -/
theorem sum_f_lower
    (C a f : ℕ → ℝ) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t) (hf_pos : ∀ t, 0 < f t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (σ_lim : ℝ) (hσ_pos : 0 < σ_lim)
    (hσ_conv : ∀ ε > 0, ∃ T, ∀ t ≥ T, |C t / (↑N₀ + ↑t) - σ_lim| ≤ ε) :
    ∃ α : ℝ, 0 < α ∧ ∃ T, ∀ t ≥ T,
      α * (↑N₀ + ↑t) ^ 2 ≤ ∑ s ∈ Finset.range t, f s := by
  obtain ⟨T₁, hT₁⟩ := eventually_f_le_C_sq C a f N₀ hN₀ δ hδ ha_lb ha_ub
    hC_pos hf_pos hC_rec σ_lim hσ_pos hσ_conv
  obtain ⟨T₂, hT₂⟩ := hσ_conv (σ_lim / 2) (by linarith)
  set T₀ := max T₁ T₂
  have hC_lb : ∀ t, t ≥ T₀ → (σ_lim / 2) * (↑N₀ + ↑t) ≤ C t := by
    intro t ht
    have hD_pos : (0 : ℝ) < ↑N₀ + ↑t := by positivity
    have hb := hT₂ t (le_trans (le_max_right T₁ T₂) ht)
    rw [abs_le] at hb
    calc (σ_lim / 2) * (↑N₀ + ↑t)
        ≤ C t / (↑N₀ + ↑t) * (↑N₀ + ↑t) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hD_pos); linarith [hb.1]
      _ = C t := div_mul_cancel₀ _ (ne_of_gt hD_pos)
  have htele := C_sq_upper_telescope C a f δ hδ ha_lb ha_ub hC_pos hf_pos hC_rec T₀
    (fun t ht => hT₁ t (le_trans (le_max_left T₁ T₂) ht))
  use (σ_lim / 2) ^ 2 / 6, by positivity
  set A := C T₀ ^ 2 with hA_def
  have hA_pos : 0 < A := sq_pos_of_pos (hC_pos T₀)
  obtain ⟨T₃, hT₃⟩ := exists_nat_gt (2 * A / (σ_lim / 2) ^ 2)
  use max T₀ T₃
  intro t ht
  have ht_T₀ : t ≥ T₀ := le_trans (le_max_left _ _) ht
  have ht_T₃ : t ≥ T₃ := le_trans (le_max_right _ _) ht
  set k := t - T₀ with hk_def
  have hk : t = T₀ + k := by omega
  have h_tele := htele k
  have h_C_lb := hC_lb t ht_T₀
  have hD_pos : (0 : ℝ) < ↑N₀ + ↑t := by positivity
  have h_C_sq_lb : (σ_lim / 2) ^ 2 * (↑N₀ + ↑t) ^ 2 ≤ C t ^ 2 := by
    have h1 : (σ_lim / 2) * (↑N₀ + ↑t) ≤ C t := h_C_lb
    have h2 : 0 ≤ (σ_lim / 2) * (↑N₀ + ↑t) := by positivity
    calc (σ_lim / 2) ^ 2 * (↑N₀ + ↑t) ^ 2
        = ((σ_lim / 2) * (↑N₀ + ↑t)) ^ 2 := by ring
      _ ≤ C t ^ 2 := sq_le_sq' (by linarith [hC_pos t]) h1
  rw [hk] at h_C_sq_lb
  have h_sum_lb : 3 * ∑ s ∈ Finset.range k, f (T₀ + s) ≥
      (σ_lim / 2) ^ 2 * (↑N₀ + ↑t) ^ 2 - A := by
    rw [hk]; nlinarith
  have hD_large : 2 * A / (σ_lim / 2) ^ 2 < (↑N₀ + ↑t) ^ 2 := by
    have hD_ge_T₃ : (↑T₃ : ℝ) ≤ (↑N₀ + ↑t) := by
      have : (↑T₃ : ℝ) ≤ ↑t := Nat.cast_le.mpr ht_T₃
      have : (0 : ℝ) ≤ ↑N₀ := Nat.cast_nonneg N₀
      linarith
    have hD_sq : (↑N₀ + ↑t : ℝ) ^ 2 ≥ (↑N₀ + ↑t : ℝ) := by
      have hD_ge1 : (1 : ℝ) ≤ (↑N₀ : ℝ) + (↑t : ℝ) := by
        have : (1 : ℝ) ≤ (↑N₀ : ℝ) := by exact_mod_cast hN₀
        linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ ↑t)]
      nlinarith [sq_nonneg (↑N₀ + ↑t - 1 : ℝ)]
    linarith
  have h_sum_split : ∑ s ∈ Finset.range t, f s ≥ ∑ s ∈ Finset.range k, f (T₀ + s) := by
    rw [hk]
    have hsplit := Finset.sum_range_add f T₀ k
    have hnn : 0 ≤ ∑ s ∈ Finset.range T₀, f s :=
      Finset.sum_nonneg (fun s _ => le_of_lt (hf_pos s))
    linarith
  have hσ_sq_pos : (0 : ℝ) < (σ_lim / 2) ^ 2 := by positivity
  have hA_small : 2 * A < (σ_lim / 2) ^ 2 * (↑N₀ + ↑t) ^ 2 := by
    have := (div_lt_iff₀ hσ_sq_pos).mp hD_large
    linarith
  nlinarith

/-! ## Main aggregate theorem -/

/-- Aggregate accumulation rigidity: Sigma_f = Theta(D^2).
    This is what the paper's proof of prop:rigidity actually establishes.
    Paper: prop:rigidity (main aggregate result). -/
theorem accumulation_rigidity_aggregate
    (C : ℕ → ℝ) (a : ℕ → ℝ) (f : ℕ → ℝ)
    (N₀ : ℕ) (hN₀ : 0 < N₀)
    (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t)
    (σ_lim : ℝ) (hσ_pos : 0 < σ_lim)
    (hσ_conv : ∀ ε > 0, ∃ T, ∀ t ≥ T, |C t / (↑N₀ + ↑t) - σ_lim| ≤ ε) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∃ T, ∀ t ≥ T,
      α * (↑N₀ + ↑t) ^ 2 ≤ ∑ s ∈ Finset.range t, f s ∧
      ∑ s ∈ Finset.range t, f s ≤ β * (↑N₀ + ↑t) ^ 2 := by
  obtain ⟨T_up, hT_up⟩ := sum_f_upper C a f N₀ hN₀ δ hδ ha_lb
    hC_pos hC_rec hf_pos σ_lim hσ_pos hσ_conv
  obtain ⟨α, hα_pos, T_lo, hT_lo⟩ := sum_f_lower C a f N₀ hN₀ δ
    hδ ha_lb ha_ub hC_pos hf_pos hC_rec σ_lim hσ_pos hσ_conv
  exact ⟨α, (2 * σ_lim) ^ 2 / (2 * δ), hα_pos, by positivity,
    max T_up T_lo, fun t ht =>
      ⟨hT_lo t (le_trans (le_max_right _ _) ht),
       hT_up t (le_trans (le_max_left _ _) ht)⟩⟩

/-! ## Superlinear case: σ → ∞ -/

/-- Σ_{s=0}^{t-1} (↑s + 1)² ≥ ↑t³ / 4 for all t ≥ 1. -/
private lemma sum_sq_cubic_lower (t : ℕ) (ht : 1 ≤ t) :
    ∑ s ∈ Finset.range t, ((s : ℝ) + 1) ^ 2 ≥ (t : ℝ) ^ 3 / 4 := by
  induction t with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : n = 0
    · subst hn; simp; norm_num
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have ih' := ih hn1
      have hn_nn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
      simp only [Nat.cast_add, Nat.cast_one] at *
      nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg (n : ℝ)]

private lemma le_of_sq_le_sq_of_nonneg {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_abs a, sq_abs b, abs_of_nonneg _ha, abs_of_nonneg hb]

/-- If f grows faster than linearly (e.g. f(t) = t^2), then C grows
    faster than Theta(t), so sigma = C/N -> infinity.
    Paper: prop:rigidity (superlinear case). -/
theorem accum_superlinear_implies_sigma_unbounded
    (C : ℕ → ℝ) (a : ℕ → ℝ) (f : ℕ → ℝ)
    (N₀ : ℕ) (hN₀ : 0 < N₀)
    (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t)
    (hf_superlinear : ∃ c > 0, ∀ t, f t ≥ c * (↑t + 1) ^ 2) :
    ∀ K > 0, ∃ T, ∀ t ≥ T, C t / (↑N₀ + ↑t) ≥ K := by
  obtain ⟨c, hc_pos, hf_lb⟩ := hf_superlinear
  have hC2_lb := accum_C_squared_lower_bound C a f δ hδ ha_lb hC_pos hC_rec hf_pos
  intro K hK
  -- Step 1: Σf(s) ≥ c · t³/4 for t ≥ 1
  have hsum_lb : ∀ t, 1 ≤ t →
      ∑ s ∈ Finset.range t, f s ≥ c * ((t : ℝ) ^ 3 / 4) := by
    intro t ht
    calc ∑ s ∈ Finset.range t, f s
        ≥ ∑ s ∈ Finset.range t, c * ((s : ℝ) + 1) ^ 2 :=
          Finset.sum_le_sum (fun s _ => hf_lb s)
      _ = c * ∑ s ∈ Finset.range t, ((s : ℝ) + 1) ^ 2 := by
          rw [← Finset.mul_sum]
      _ ≥ c * ((t : ℝ) ^ 3 / 4) :=
          mul_le_mul_of_nonneg_left (sum_sq_cubic_lower t ht) (le_of_lt hc_pos)
  -- Step 2: C(t)² ≥ δc·t³/2 for t ≥ 1
  have hC2_cubic : ∀ t, 1 ≤ t → C t ^ 2 ≥ δ * c * (t : ℝ) ^ 3 / 2 := by
    intro t ht
    have h1 := hC2_lb t
    have h2 := hsum_lb t ht
    have : C 0 ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  -- Step 3: Find T such that C(t)/(N₀+t) ≥ K
  have hdc_pos : 0 < δ * c := mul_pos hδ hc_pos
  obtain ⟨T₁, hT₁⟩ := exists_nat_ge (8 * K ^ 2 / (δ * c))
  use max T₁ (max 1 N₀)
  intro t ht
  have ht1 : 1 ≤ t := by omega
  have htN₀ : N₀ ≤ t := by omega
  have hNt_pos : (0 : ℝ) < ↑N₀ + ↑t := by positivity
  rw [ge_iff_le, le_div_iff₀ hNt_pos]
  apply le_of_sq_le_sq_of_nonneg (by positivity) (le_of_lt (hC_pos t))
  have hC2 := hC2_cubic t ht1
  have hNt_le : (↑N₀ : ℝ) + ↑t ≤ 2 * ↑t := by
    have : (↑N₀ : ℝ) ≤ ↑t := Nat.cast_le.mpr htN₀
    linarith
  have hKNt_sq : (K * (↑N₀ + ↑t)) ^ 2 ≤ (K * (2 * ↑t)) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [mul_pos hK hNt_pos]
    · apply mul_le_mul_of_nonneg_left hNt_le (le_of_lt hK)
  have htT₁ : T₁ ≤ t := by omega
  have hT₁_cast : (↑T₁ : ℝ) ≤ ↑t := Nat.cast_le.mpr htT₁
  have hdc_t : δ * c * ↑t ≥ 8 * K ^ 2 := by
    have : δ * c * ↑T₁ ≥ δ * c * (8 * K ^ 2 / (δ * c)) := by
      apply mul_le_mul_of_nonneg_left hT₁ (le_of_lt hdc_pos)
    rw [mul_div_cancel₀ _ (ne_of_gt hdc_pos)] at this
    calc δ * c * ↑t ≥ δ * c * ↑T₁ := by
            apply mul_le_mul_of_nonneg_left hT₁_cast (le_of_lt hdc_pos)
      _ ≥ 8 * K ^ 2 := this
  have h4K2t2 : (K * (2 * ↑t)) ^ 2 ≤ δ * c * (↑t : ℝ) ^ 3 / 2 := by
    have ht_nn : (0 : ℝ) ≤ ↑t := Nat.cast_nonneg t
    nlinarith [sq_nonneg ((t : ℝ)), sq_nonneg K]
  linarith

/-! ## Sublinear case: σ → 0 -/

/-- If C(t) ≥ ε'·D(t) throughout [T, T+k), then C(T+k) ≤ C(T) + k·(η/ε').
    The key: increment a·f/C ≤ 1·(η·D)/(ε'·D) = η/ε'. -/
private theorem C_slow_growth
    (C a f : ℕ → ℝ) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t)
    (ε' η : ℝ) (hε' : 0 < ε') (hη : 0 < η)
    (T : ℕ) (hfη : ∀ t ≥ T, f t ≤ η * (↑t + 1))
    (k : ℕ) (hσ_ge : ∀ j < k, C (T + j) ≥ ε' * (↑(T + j) + ↑N₀)) :
    C (T + k) ≤ C T + ↑k * (η / ε') := by
  induction k with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hσ_ge j (lt_trans hj (Nat.lt_succ_of_le (le_refl n))))
    have hσ_n := hσ_ge n (Nat.lt_succ_of_le (le_refl n))
    have h_eq : T + (n + 1) = (T + n) + 1 := by omega
    rw [h_eq, hC_rec (T + n)]
    have hN₀_ge_1 : (1 : ℝ) ≤ ↑N₀ := Nat.one_le_cast.mpr hN₀
    have hf_bd : f (T + n) ≤ η * (↑(T + n) + ↑N₀) := by
      calc f (T + n) ≤ η * (↑(T + n) + 1) := hfη (T + n) (Nat.le_add_right T n)
        _ ≤ η * (↑(T + n) + ↑N₀) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hη); linarith
    have h_num : a (T + n) * f (T + n) ≤ η * (↑(T + n) + ↑N₀) := by
      calc a (T + n) * f (T + n) ≤ 1 * f (T + n) :=
            mul_le_mul_of_nonneg_right (ha_ub (T + n)) (le_of_lt (hf_pos (T + n)))
        _ = f (T + n) := one_mul _
        _ ≤ η * (↑(T + n) + ↑N₀) := hf_bd
    have h_inc : a (T + n) * f (T + n) / C (T + n) ≤ η / ε' := by
      rw [div_le_div_iff₀ (hC_pos (T + n)) hε']
      nlinarith [mul_le_mul_of_nonneg_left hσ_n (le_of_lt hη),
                 mul_le_mul_of_nonneg_right h_num (le_of_lt hε')]
    calc C (T + n) + a (T + n) * f (T + n) / C (T + n)
        ≤ C (T + n) + η / ε' := by linarith
      _ ≤ (C T + ↑n * (η / ε')) + η / ε' := by linarith
      _ = C T + ↑(n + 1) * (η / ε') := by push_cast; ring

/-- Since C grows by ≤ η/ε' per step but D grows by 1 per step, and η/ε' < ε',
    the ratio σ = C/D must eventually drop below ε'. -/
private theorem sigma_drops_below
    (C a f : ℕ → ℝ) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t)
    (ε' η : ℝ) (hε' : 0 < ε') (hη : 0 < η) (hηε : η < ε' ^ 2)
    (T : ℕ) (hfη : ∀ t ≥ T, f t ≤ η * (↑t + 1)) :
    ∃ t ≥ T, C t / (↑t + ↑N₀) < ε' := by
  by_contra h; push_neg at h
  have hσ_all : ∀ k, C (T + k) ≥ ε' * (↑(T + k) + ↑N₀) := by
    intro k
    have hD_pos : (0 : ℝ) < ↑(T + k) + ↑N₀ := by positivity
    have h1 := h (T + k) (Nat.le_add_right T k)
    rwa [ge_iff_le, ← le_div_iff₀ hD_pos]
  have hC_ub : ∀ k, C (T + k) ≤ C T + ↑k * (η / ε') :=
    fun k => C_slow_growth C a f N₀ hN₀ ha_ub hC_pos hC_rec hf_pos
      ε' η hε' hη T hfη k (fun j _ => hσ_all j)
  have hε'_net : 0 < ε' - η / ε' := by rw [sub_pos, div_lt_iff₀ hε']; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (C T / (ε' - η / ε'))
  have h1 := hσ_all k; have h2 := hC_ub k
  have : ↑k * (ε' - η / ε') ≤ C T := by
    have expand : ε' * (↑(T + k) + ↑N₀) = ε' * (↑T + ↑N₀) + ε' * ↑k := by push_cast; ring
    nlinarith [mul_nonneg (le_of_lt hε') (show (0:ℝ) ≤ ↑T + ↑N₀ from by positivity)]
  linarith [show C T < ↑k * (ε' - η / ε') from by rwa [div_lt_iff₀ hε'_net] at hk]

/-- Once C(t₀) < M·D(t₀), C(t) ≤ M·D(t) for all t ≥ t₀. -/
private theorem sigma_barrier
    (C a f : ℕ → ℝ) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t)
    (ε' η M : ℝ) (hε' : 0 < ε') (hη : 0 < η)
    (hηε'_sq : η ≤ ε' ^ 2)
    (hM_def : M = ε' + η / C 0)
    (t : ℕ)
    (hfη_t : f t ≤ η * (↑t + 1))
    (hCt : C t ≤ M * (↑t + ↑N₀)) :
    C (t + 1) ≤ M * (↑(t + 1) + ↑N₀) := by
  rw [hC_rec t]
  have hD_pos : (0 : ℝ) < ↑t + ↑N₀ := by positivity
  have hC_pos_t := hC_pos t
  have hN₀_ge_1 : (1 : ℝ) ≤ ↑N₀ := Nat.one_le_cast.mpr hN₀
  have hf_bd : f t ≤ η * (↑t + ↑N₀) := by
    calc f t ≤ η * (↑t + 1) := hfη_t
      _ ≤ η * (↑t + ↑N₀) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hη); linarith
  have hC0_pos := hC_pos 0
  have hM_pos : 0 < M := by
    rw [hM_def]; linarith [div_pos hη hC0_pos]
  by_cases hσ : C t ≥ ε' * (↑t + ↑N₀)
  · have h_inc : a t * f t / C t ≤ η / ε' := by
      rw [div_le_div_iff₀ hC_pos_t hε']
      have h_af : a t * f t ≤ η * (↑t + ↑N₀) := by
        calc a t * f t ≤ 1 * f t :=
              mul_le_mul_of_nonneg_right (ha_ub t) (le_of_lt (hf_pos t))
          _ = f t := one_mul _
          _ ≤ η * (↑t + ↑N₀) := hf_bd
      nlinarith [mul_le_mul_of_nonneg_left hσ (le_of_lt hη),
                 mul_le_mul_of_nonneg_right h_af (le_of_lt hε')]
    have h_ηε'_le_ε' : η / ε' ≤ ε' := by
      rw [div_le_iff₀ hε']; linarith [hηε'_sq]
    have h_ε'_le_M : ε' ≤ M := by
      rw [hM_def]; linarith [div_pos hη hC0_pos]
    calc C t + a t * f t / C t
        ≤ C t + η / ε' := by linarith
      _ ≤ M * (↑t + ↑N₀) + M := by linarith [h_ε'_le_M]
      _ = M * (↑t + ↑N₀ + 1) := by ring
      _ = M * (↑(t + 1) + ↑N₀) := by push_cast; ring
  · push_neg at hσ
    have hC0_le : C 0 ≤ C t :=
      C_mono_le C a f δ hδ ha_lb hC_pos hf_pos hC_rec 0 t (Nat.zero_le t)
    have h_inc : a t * f t / C t ≤ η / C 0 * (↑t + ↑N₀) := by
      have h1 : a t * f t / C t ≤ f t / C 0 := by
        rw [div_le_div_iff₀ hC_pos_t hC0_pos]
        have h_step1 : a t * f t ≤ f t := by nlinarith [ha_ub t, hf_pos t]
        nlinarith [mul_le_mul_of_nonneg_left hC0_le (le_of_lt (hf_pos t))]
      calc a t * f t / C t ≤ f t / C 0 := h1
        _ ≤ (η * (↑t + ↑N₀)) / C 0 :=
            div_le_div_of_nonneg_right hf_bd (le_of_lt hC0_pos)
        _ = η / C 0 * (↑t + ↑N₀) := by ring
    calc C t + a t * f t / C t
        ≤ C t + η / C 0 * (↑t + ↑N₀) := by linarith
      _ ≤ ε' * (↑t + ↑N₀) + η / C 0 * (↑t + ↑N₀) := by nlinarith
      _ = (ε' + η / C 0) * (↑t + ↑N₀) := by ring
      _ = M * (↑t + ↑N₀) := by rw [hM_def]
      _ ≤ M * (↑(t + 1) + ↑N₀) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hM_pos)
          push_cast; linarith

/-- If f is sublinear (f = o(t)), then sigma = C/D -> 0.
    Uses a sigma-decrease argument: C grows slowly (<= eta/eps' per step)
    while D grows by 1, forcing sigma below any threshold.
    Paper: prop:rigidity (sublinear case). -/
theorem accum_sublinear_implies_sigma_zero
    (C : ℕ → ℝ) (a : ℕ → ℝ) (f : ℕ → ℝ)
    (N₀ : ℕ) (hN₀ : 0 < N₀)
    (δ : ℝ) (hδ : 0 < δ)
    (ha_lb : ∀ t, δ ≤ a t) (ha_ub : ∀ t, a t ≤ 1)
    (hC_pos : ∀ t, 0 < C t)
    (hC_rec : ∀ t, C (t + 1) = C t + a t * f t / C t)
    (hf_pos : ∀ t, 0 < f t)
    (hf_sub : ∀ ε > 0, ∃ T, ∀ t ≥ T, f t ≤ ε * (↑t + 1)) :
    ∀ ε > 0, ∃ T, ∀ t ≥ T, C t / (↑N₀ + ↑t) ≤ ε := by
  intro ε hε
  set ε' := ε / 2 with hε'_def
  have hε' : 0 < ε' := by positivity
  set η := min (ε' ^ 2 / 2) (ε' * C 0 / 2) with hη_def
  have hC0_pos := hC_pos 0
  have hη : 0 < η := by
    simp only [hη_def]; exact lt_min (by positivity) (by positivity)
  have hηε : η < ε' ^ 2 := by
    calc η ≤ ε' ^ 2 / 2 := min_le_left _ _
      _ < ε' ^ 2 := by linarith [sq_pos_of_pos hε']
  have hηε_le : η ≤ ε' ^ 2 := le_of_lt hηε
  have hη_boost : η / C 0 ≤ ε' / 2 := by
    rw [div_le_div_iff₀ hC0_pos (by positivity : (0:ℝ) < 2)]
    linarith [min_le_right (ε' ^ 2 / 2) (ε' * C 0 / 2)]
  set M := ε' + η / C 0 with hM_def
  have hM_le_ε : M ≤ ε := by
    simp only [hM_def, hε'_def]; linarith
  obtain ⟨T₁, hT₁⟩ := hf_sub η hη
  obtain ⟨t₀, ht₀, hσ_t₀⟩ := sigma_drops_below C a f N₀ hN₀ ha_ub
    hC_pos hC_rec hf_pos ε' η hε' hη hηε T₁ hT₁
  have hC_t₀ : C t₀ < M * (↑t₀ + ↑N₀) := by
    have hD_pos : (0 : ℝ) < ↑t₀ + ↑N₀ := by positivity
    have : C t₀ < ε' * (↑t₀ + ↑N₀) := by rwa [div_lt_iff₀ hD_pos] at hσ_t₀
    calc C t₀ < ε' * (↑t₀ + ↑N₀) := this
      _ ≤ M * (↑t₀ + ↑N₀) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hD_pos)
        simp only [hM_def]; linarith [div_pos hη hC0_pos]
  use t₀; intro t ht
  have hD_pos : (0 : ℝ) < ↑N₀ + ↑t := by positivity
  rw [div_le_iff₀ hD_pos]
  suffices h : C t ≤ M * (↑t + ↑N₀) by
    calc C t ≤ M * (↑t + ↑N₀) := h
      _ ≤ ε * (↑t + ↑N₀) := by nlinarith
      _ = ε * (↑N₀ + ↑t) := by ring
  have hbar : ∀ n, C (t₀ + n) ≤ M * (↑(t₀ + n) + ↑N₀) := by
    intro n; induction n with
    | zero => simp; linarith
    | succ m ih =>
      have h_eq : t₀ + (m + 1) = (t₀ + m) + 1 := by omega
      rw [h_eq]
      exact sigma_barrier C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec hf_pos
        ε' η M hε' hη hηε_le hM_def (t₀ + m)
        (hT₁ (t₀ + m) (le_trans ht₀ (Nat.le_add_right t₀ m))) ih
  have hk : t = t₀ + (t - t₀) := by omega
  rw [hk]; exact hbar (t - t₀)

