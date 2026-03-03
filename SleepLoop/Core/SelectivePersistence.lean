/-
  SleepLoop/Core/SelectivePersistence.lean

  Theorem 2 (thm:selective): Selective persistence.
  (i) If a_t(tau) = 0 for all t >= T, then sigma_t(tau) -> 0.
  (ii) If a_t(tau) >= delta > 0 for all t, then liminf sigma_t(tau) >= sqrt(delta).
  (iii) For any attention sequence in [0,1], sigma_t(tau) = O(1).
  Level: 𝒜.
-/
import SleepLoop.Defs.Accumulation
import SleepLoop.Defs.LoopState
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! ## Selective Persistence -/

variable {X : Type*} [Fintype X]

omit [Fintype X] in
/-- thm:selective (i): If attention ceases after time T, salience decays to 0.
    If a_t(τ) = 0 for all t ≥ T, then σ_t(τ) → 0. -/
theorem selective_persistence_decay
    (C : ℕ → X → ℝ) (N : ℕ → X → ℕ) (a : ℕ → X → ℝ)
    (τ : X) (T : ℕ)
    (hC_pos : ∀ t, 0 < C t τ)
    (hN_pos : ∀ t, 0 < N t τ)
    (h_update_C : ∀ t, C (t + 1) τ = accumulateC (C t) (a t) t τ)
    (h_update_N : ∀ t, N (t + 1) τ = N t τ + 1)
    (h_cease : ∀ t, T ≤ t → a t τ = 0) :
    Filter.Tendsto (fun t => C t τ / (N t τ : ℝ)) Filter.atTop (nhds 0) := by
  -- Step 1: Show C is constant after time T
  have hC_const : ∀ t, T ≤ t → C t τ = C T τ := by
    intro t
    induction t with
    | zero =>
      intro ht
      have hT0 : T = 0 := by omega
      subst hT0; rfl
    | succ n ih =>
      intro ht
      by_cases hn : T ≤ n
      · rw [h_update_C n]
        unfold accumulateC
        rw [h_cease n hn, ih hn]
        simp [zero_mul, zero_div, add_zero]
      · have hTn : T = n + 1 := by omega
        rw [hTn]
  -- Step 2: N grows linearly
  have hN_grow : ∀ t, N t τ = N 0 τ + t := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [h_update_N n, ih]; omega
  -- Step 3: For t ≥ T, the ratio equals C T τ / (N 0 τ + t)
  -- Use squeeze theorem: 0 ≤ C t τ / N t τ ≤ C T τ / (N 0 τ + t) for t ≥ T
  -- and the upper bound → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- We need: ∃ N₀, ∀ t ≥ N₀, |C t τ / N t τ - 0| < ε
  -- For t ≥ T: C t τ / N t τ = C T τ / (N 0 τ + t)
  -- Choose N₀ large enough that C T τ / (N 0 τ + t) < ε
  -- i.e., C T τ / ε < N 0 τ + t, i.e., t > C T τ / ε - N 0 τ
  obtain ⟨k, hk⟩ := exists_nat_ge (max (T : ℝ) (C T τ / ε))
  use k
  intro t ht
  rw [Real.dist_eq, sub_zero]
  -- |C t τ / N t τ| = C t τ / N t τ (since both positive)
  have hN_t_pos : (0 : ℝ) < (N t τ : ℝ) := Nat.cast_pos.mpr (hN_pos t)
  have hC_t_pos : 0 < C t τ := hC_pos t
  rw [abs_of_pos (div_pos hC_t_pos hN_t_pos)]
  -- For t ≥ T (which holds since t ≥ k ≥ T):
  have hT_le_k : (T : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
  have ht_ge_T : T ≤ t := by exact_mod_cast le_trans hT_le_k (Nat.cast_le.mpr ht)
  rw [hC_const t ht_ge_T]
  -- Goal: C T τ / N t τ < ε
  rw [div_lt_iff₀ hN_t_pos]
  -- Goal: C T τ < ε * N t τ
  rw [hN_grow t]
  have hCT_ε_le_k : C T τ / ε ≤ (k : ℝ) := le_trans (le_max_right _ _) hk
  have hk_le_t : (k : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr ht
  have hN0_pos : (0 : ℝ) < (N 0 τ : ℝ) := Nat.cast_pos.mpr (hN_pos 0)
  -- C T τ / ε ≤ k ≤ t, so C T τ ≤ ε * t < ε * (N 0 τ + t)
  have hCT_le_kε : C T τ ≤ (k : ℝ) * ε := (div_le_iff₀ hε).mp hCT_ε_le_k
  push_cast
  nlinarith

omit [Fintype X] in
/-- thm:selective (ii): If attention is bounded below by δ > 0,
    then liminf σ_t(τ) ≥ √δ. -/
theorem selective_persistence_growth
    (C : ℕ → X → ℝ) (N : ℕ → X → ℕ) (a : ℕ → X → ℝ)
    (τ : X) (δ : ℝ) (hδ : 0 < δ)
    (hC_pos : ∀ t, 0 < C t τ)
    (h_update_C : ∀ t, C (t + 1) τ = accumulateC (C t) (a t) t τ)
    (h_update_N : ∀ t, N (t + 1) τ = N t τ + 1)
    (h_lower : ∀ t, δ ≤ a t τ) :
    ∀ ε > 0, ∃ T, ∀ t ≥ T, C t τ / (N t τ : ℝ) ≥ Real.sqrt δ - ε := by
  -- Paper proof outline:
  -- Step 1: C(t+1)² = C(t)² + 2·a_t·(t+1) + a_t²·(t+1)²/C(t)²
  --         ≥ C(t)² + 2·δ·(t+1)  (since a_t ≥ δ)
  -- Step 2: By induction, C(t)² ≥ C(0)² + δ·t·(t+1)
  -- Step 3: C(t) ≥ √(δ·t·(t+1))
  -- Step 4: σ(t) = C(t)/(N(0)+t) ≥ √(δ·t·(t+1))/(N(0)+t) → √δ

  -- Key lemma: C squared grows at least quadratically
  have hC_sq_lower : ∀ (t : ℕ), C 0 τ ^ 2 + δ * (t : ℝ) * ((t : ℝ) + 1) ≤ C t τ ^ 2 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      push_cast [Nat.cast_succ]
      have h_rec := h_update_C n
      unfold accumulateC at h_rec
      -- C(n+1) = C(n) + a(n) * (n+1) / C(n)
      -- C(n+1)² = C(n)² + 2·a(n)·(n+1) + a(n)²·(n+1)²/C(n)²
      have hCn_pos : 0 < C n τ := hC_pos n
      have hCn_ne : C n τ ≠ 0 := ne_of_gt hCn_pos
      have h_sq : C (n + 1) τ ^ 2 = C n τ ^ 2 + 2 * (a n τ) * ((n : ℝ) + 1) +
          (a n τ) ^ 2 * ((n : ℝ) + 1) ^ 2 / (C n τ) ^ 2 := by
        have hCn_sq_ne : (C n τ) ^ 2 ≠ 0 := pow_ne_zero 2 hCn_ne
        rw [h_rec]; field_simp [hCn_ne]; ring
      -- The last term is nonneg
      have h_last_nn : 0 ≤ (a n τ) ^ 2 * ((n : ℝ) + 1) ^ 2 / (C n τ) ^ 2 := by
        positivity
      -- 2·a(n)·(n+1) ≥ 2·δ·(n+1)
      have h_delta_bound : 2 * δ * ((n : ℝ) + 1) ≤ 2 * (a n τ) * ((n : ℝ) + 1) := by
        have := h_lower n
        nlinarith
      calc C 0 τ ^ 2 + δ * ((n : ℝ) + 1) * (((n : ℝ) + 1) + 1)
          = (C 0 τ ^ 2 + δ * (n : ℝ) * ((n : ℝ) + 1)) + 2 * δ * ((n : ℝ) + 1) := by ring
        _ ≤ C n τ ^ 2 + 2 * (a n τ) * ((n : ℝ) + 1) := by linarith [ih, h_delta_bound]
        _ ≤ C n τ ^ 2 + 2 * (a n τ) * ((n : ℝ) + 1) +
            (a n τ) ^ 2 * ((n : ℝ) + 1) ^ 2 / (C n τ) ^ 2 := by linarith [h_last_nn]
        _ = C (n + 1) τ ^ 2 := h_sq.symm
  -- N grows linearly
  have hN_grow : ∀ t, N t τ = N 0 τ + t := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [h_update_N n, ih]; omega
  -- Now show the liminf property
  intro ε hε
  -- From hC_sq_lower, C(t) >= sqrt(delta * t * (t+1))
  have hC_lower : ∀ (t : ℕ), Real.sqrt (δ * (t : ℝ) * ((t : ℝ) + 1)) ≤ C t τ := by
    intro t
    rw [← Real.sqrt_sq (le_of_lt (hC_pos t))]
    apply Real.sqrt_le_sqrt
    have h := hC_sq_lower t
    nlinarith
  set N₀ := N 0 τ
  -- N(t) = N₀ + t
  -- Derive N(t) > 0: N(t) = N₀ + t ≥ 0 + 1 = 1 for t ≥ 1, and for t = 0, N₀ ≥ 1
  -- Actually we need N(t) > 0. From h_update_N, N grows. But N₀ could be 0.
  -- However, if N₀ = 0 then C 0 τ / 0 is 0/0 = 0, and we need C(t)/(N₀+t) ≥ √δ-ε.
  -- For t ≥ 1: N(t) = N₀ + t ≥ 1. And C(t) ≥ √(δ·t·(t+1)). So the ratio works.
  -- For t = 0 with N₀ = 0: ratio = C(0)/0 = 0 (by convention), but we can start from T ≥ 1.

  -- If √δ ≤ ε, trivial
  by_cases hε_large : Real.sqrt δ ≤ ε
  · use 1; intro t ht
    have hNt_pos : (0 : ℝ) < ↑(N t τ) := by
      rw [Nat.cast_pos, hN_grow t]; omega
    have : 0 < C t τ / (↑(N t τ) : ℝ) := div_pos (hC_pos t) hNt_pos
    linarith
  · push_neg at hε_large
    set sqde := Real.sqrt δ - ε
    have hsqde_pos : 0 < sqde := by linarith
    set c := δ - sqde ^ 2
    have hc_pos : 0 < c := by
      change 0 < δ - sqde ^ 2
      have h1 : sqde < Real.sqrt δ := by linarith
      have h2 : 0 < sqde := hsqde_pos
      have h3 : sqde ^ 2 < (Real.sqrt δ) ^ 2 := by nlinarith
      rw [Real.sq_sqrt (le_of_lt hδ)] at h3; linarith
    -- Choose T large enough that c * T >= sqde^2 * (N₀+1)^2
    obtain ⟨T₀, hT₀⟩ := exists_nat_ge (sqde ^ 2 * ((N₀ : ℝ) + 1) ^ 2 / c)
    use max T₀ 1
    intro t ht
    have ht1 : 1 ≤ t := le_trans (le_max_right T₀ 1) ht
    have htT₀ : T₀ ≤ t := le_trans (le_max_left T₀ 1) ht
    rw [ge_iff_le, hN_grow t]
    have hNt_pos : (0 : ℝ) < ↑(N₀ + t) := Nat.cast_pos.mpr (by omega)
    rw [le_div_iff₀ hNt_pos]
    -- Goal: sqde * (N₀ + t) ≤ C t τ
    -- Suffices: sqde * (N₀ + t) ≤ √(δ·t·(t+1)) ≤ C t τ
    calc sqde * ↑(N₀ + t) ≤ Real.sqrt (δ * (t : ℝ) * ((t : ℝ) + 1)) := by
          -- Show by squaring (both sides nonneg)
          have h_sqde_mul_nn : (0 : ℝ) ≤ sqde * ↑(N₀ + t) := by
            apply mul_nonneg (le_of_lt hsqde_pos) (Nat.cast_nonneg _)
          rw [← Real.sqrt_sq h_sqde_mul_nn]
          apply Real.sqrt_le_sqrt
          -- (sqde * (N₀+t))^2 ≤ δ * t * (t+1)
          rw [mul_pow]
          push_cast
          -- sqde^2 * (N₀+t)^2 ≤ (sqde^2 + c) * t * (t+1)
          -- Need: sqde^2 * (N₀+t)^2 ≤ δ * t * (t+1) = (sqde^2 + c) * t * (t+1)
          -- Expanding: sqde^2 * (t^2 + 2N₀t + N₀^2) ≤ sqde^2 * (t^2+t) + c*t*(t+1)
          -- sqde^2 * (2N₀t + N₀^2 - t) ≤ c*t*(t+1)
          -- sqde^2 * ((2N₀-1)*t + N₀^2) ≤ c*t*(t+1)
          -- For t ≥ 1: (2N₀-1)*t + N₀^2 ≤ (N₀+1)^2 * t  (since N₀^2 ≤ (N₀^2+2N₀+1-2N₀+1-1)t ...)
          -- Actually: (2N₀-1)*t + N₀^2 ≤ 2N₀*t + N₀^2 ≤ (N₀+1)^2 * t when t ≥ N₀^2 or using ct
          -- Key: c*t ≥ c*T₀ ≥ sqde^2*(N₀+1)^2 from hT₀
          -- and c*t*(t+1) ≥ c*t ≥ sqde^2*(N₀+1)^2
          -- We need sqde^2*((2N₀-1)*t + N₀^2) ≤ c*t*(t+1)
          -- Using c*t*(t+1) = c*t^2 + c*t and c*t ≥ sqde^2*(N₀+1)^2:
          -- c*t^2 ≥ sqde^2*(N₀+1)^2 * t  and c*t ≥ sqde^2*(N₀+1)^2
          -- Sum: c*t*(t+1) ≥ sqde^2*(N₀+1)^2*(t+1)
          -- And (N₀+1)^2*(t+1) = (N₀^2+2N₀+1)*(t+1) ≥ (2N₀+1)*t + N₀^2 + t + 1
          -- ≥ (2N₀-1)*t + N₀^2 + 2t + 1 ≥ (2N₀-1)*t + N₀^2. Done.
          have hcT : sqde ^ 2 * ((N₀ : ℝ) + 1) ^ 2 ≤ c * (t : ℝ) := by
            have h1 : sqde ^ 2 * ((N₀ : ℝ) + 1) ^ 2 / c ≤ (T₀ : ℝ) := hT₀
            have h2 : sqde ^ 2 * ((N₀ : ℝ) + 1) ^ 2 ≤ (T₀ : ℝ) * c :=
              (div_le_iff₀ hc_pos).mp h1
            have h3 : (T₀ : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr htT₀
            nlinarith
          -- Show: sqde^2 * (N₀+t)^2 ≤ δ * t * (t+1)
          -- δ * t * (t+1) = (sqde^2 + c) * t * (t+1)
          --   = sqde^2 * t * (t+1) + c * t * (t+1)
          -- (N₀+t)^2 = t^2 + 2*N₀*t + N₀^2
          -- So need: sqde^2 * (2*N₀*t + N₀^2) ≤ sqde^2 * t + c * t * (t+1)
          -- From hcT: c*t ≥ sqde^2*(N₀+1)^2 = sqde^2*(N₀^2+2*N₀+1)
          -- So c*t*(t+1) = c*t*t + c*t ≥ sqde^2*(N₀^2+2*N₀+1)*t + sqde^2*(N₀^2+2*N₀+1)
          -- And sqde^2*t + c*t*(t+1) ≥ sqde^2*t + sqde^2*(N₀^2+2*N₀+1)*t + sqde^2*(N₀^2+2*N₀+1)
          --   = sqde^2*(t + (N₀^2+2*N₀+1)*t + N₀^2+2*N₀+1)
          --   = sqde^2*((N₀^2+2*N₀+2)*t + N₀^2+2*N₀+1)
          -- Need (N₀^2+2*N₀+2)*t + N₀^2+2*N₀+1 ≥ 2*N₀*t + N₀^2
          --   ↔ (N₀^2+2)*t + 2*N₀+1 ≥ 0, which is always true. Done!
          have hN₀_nn : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
          have ht_nn : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
          have ht1_cast : (1 : ℝ) ≤ (t : ℝ) := Nat.one_le_cast.mpr ht1
          -- δ = sqde^2 + c
          have hd : δ = sqde ^ 2 + c := by simp only [c]; ring
          -- From hcT, derive: c*t^2 ≥ sqde^2*(N₀+1)^2*t
          have hctt : sqde ^ 2 * ((N₀ : ℝ) + 1) ^ 2 * (t : ℝ) ≤ c * (t : ℝ) ^ 2 := by
            have : sqde ^ 2 * ((N₀ : ℝ) + 1) ^ 2 * (t : ℝ) ≤ c * (t : ℝ) * (t : ℝ) := by
              nlinarith [hcT]
            linarith [sq (t : ℝ)]
          -- Goal: sqde^2 * (↑N₀ + ↑t)^2 ≤ δ * ↑t * (↑t + 1)
          -- Rewrite δ, expand, and use hctt and hcT
          -- sqde^2*(N₀+t)^2 = sqde^2*(t^2 + 2*N₀*t + N₀^2)
          -- δ*t*(t+1) = sqde^2*t*(t+1) + c*t*(t+1) = sqde^2*t^2 + sqde^2*t + c*t^2 + c*t
          -- Diff = sqde^2*t + c*t^2 + c*t - sqde^2*2*N₀*t - sqde^2*N₀^2
          -- ≥ sqde^2*t + sqde^2*(N₀+1)^2*t + sqde^2*(N₀+1)^2 - sqde^2*2*N₀*t - sqde^2*N₀^2
          -- = sqde^2*[t + (N₀^2+2*N₀+1)*t + N₀^2+2*N₀+1 - 2*N₀*t - N₀^2]
          -- = sqde^2*[(N₀^2+1)*t + 2*N₀+1]
          -- ≥ 0
          -- Provide the expanded difference as a have
          suffices h : sqde ^ 2 * (t : ℝ) + c * (t : ℝ) ^ 2 + c * (t : ℝ) ≥
              sqde ^ 2 * (2 * (N₀ : ℝ) * (t : ℝ) + (N₀ : ℝ) ^ 2) by nlinarith [sq (t : ℝ)]
          -- Use hctt and hcT
          calc sqde ^ 2 * (2 * (N₀ : ℝ) * (t : ℝ) + (N₀ : ℝ) ^ 2)
              ≤ sqde ^ 2 * (((N₀ : ℝ) + 1) ^ 2 * (t : ℝ) + ((N₀ : ℝ) + 1) ^ 2) := by
                apply mul_le_mul_of_nonneg_left _ (sq_nonneg sqde)
                nlinarith [sq_nonneg (N₀ : ℝ)]
            _ ≤ c * (t : ℝ) ^ 2 + c * (t : ℝ) := by linarith [hctt, hcT]
            _ ≤ sqde ^ 2 * (t : ℝ) + c * (t : ℝ) ^ 2 + c * (t : ℝ) := by
                nlinarith [sq_nonneg sqde]
      _ ≤ C t τ := hC_lower t

omit [Fintype X] in
/-- thm:selective (iii): For any attention sequence in [0,1], σ_t(τ) = O(1).
    Uses: the increment a_t*(t+1)/C_t satisfies a_t*(t+1)/C_t ≤ (t+1)/C_t,
    and by AM-GM, C_t + (t+1)/C_t ≥ 2√(t+1), so after each step the ratio
    C/N stays self-regulated. -/
theorem selective_persistence_bounded
    (C : ℕ → X → ℝ) (N : ℕ → X → ℕ) (a : ℕ → X → ℝ)
    (τ : X)
    (hC_pos : ∀ t, 0 < C t τ)
    (h_update_C : ∀ t, C (t + 1) τ = accumulateC (C t) (a t) t τ)
    (h_update_N : ∀ t, N (t + 1) τ = N t τ + 1)
    (h_range : ∀ t, 0 ≤ a t τ ∧ a t τ ≤ 1) :
    ∃ B : ℝ, ∀ t, C t τ / (N t τ : ℝ) ≤ B := by
  have hN_grow : ∀ t, N t τ = N 0 τ + t := by
    intro t; induction t with
    | zero => simp
    | succ n ih => rw [h_update_N n, ih]; omega
  set N₀ := N 0 τ
  have hC_nondec : ∀ t, C t τ ≤ C (t + 1) τ := by
    intro t; rw [h_update_C t]; unfold accumulateC
    linarith [div_nonneg (mul_nonneg (h_range t).1
      (by positivity : (0 : ℝ) ≤ (t : ℝ) + 1)) (le_of_lt (hC_pos t))]
  have hC_ge_C0 : ∀ t, C 0 τ ≤ C t τ := by
    intro t; induction t with
    | zero => exact le_refl _
    | succ n ih => exact le_trans ih (hC_nondec n)
  have hC_upd : ∀ t, C (t + 1) τ = C t τ + a t τ * ((t : ℝ) + 1) / C t τ := by
    intro t; rw [h_update_C t]; rfl
  have hC0 : 0 < C 0 τ := hC_pos 0
  -- Main claim by strong induction: C(t) <= B*(N₀+t) when N₀+t >= 1
  -- where B = C(0) + 1/C(0) + 2
  have h_main : ∀ t, 1 ≤ N₀ + t →
      C t τ ≤ (C 0 τ + 1 / C 0 τ + 2) * ↑(N₀ + t) := by
    intro t; induction t with
    | zero =>
      intro h1
      calc C 0 τ ≤ (C 0 τ + 1 / C 0 τ + 2) * 1 := by linarith [div_pos one_pos hC0]
        _ ≤ (C 0 τ + 1 / C 0 τ + 2) * ↑N₀ := by
            apply mul_le_mul_of_nonneg_left (Nat.one_le_cast.mpr h1)
            linarith [div_pos one_pos hC0]
    | succ n ih =>
      intro h1; rw [hC_upd n]
      by_cases hn0 : N₀ + n = 0
      · -- N₀ = 0 and n = 0
        have hn : n = 0 := by omega
        subst hn
        have hN₀z : N₀ = 0 := by omega
        have hincr : a 0 τ * ((0 : ℝ) + 1) / C 0 τ ≤ 1 / C 0 τ := by
          apply div_le_div_of_nonneg_right _ hC0.le; nlinarith [(h_range 0).1, (h_range 0).2]
        simp only [hN₀z, Nat.zero_add, Nat.cast_one, mul_one]
        push_cast
        linarith
      · -- N₀ + n >= 1, IH applies
        specialize ih (by omega : 1 ≤ N₀ + n)
        have hCn : 0 < C n τ := hC_pos n
        have hNn : (0 : ℝ) < ↑(N₀ + n) := Nat.cast_pos.mpr (by omega)
        have hNn1 : (↑(N₀ + (n + 1)) : ℝ) = ↑(N₀ + n) + 1 := by push_cast; ring
        rw [hNn1]
        -- Case: sigma >= 2 vs sigma < 2
        by_cases hσ : 2 * ↑(N₀ + n) ≤ C n τ
        · -- Self-regulation: a*(n+1)/C(n) <= C(n)/(N₀+n)
          have h_key : a n τ * ((n : ℝ) + 1) * ↑(N₀ + n) ≤ C n τ ^ 2 := by
            have hNn_ge1 : (1 : ℝ) ≤ ↑(N₀ + n) := Nat.one_le_cast.mpr (by omega)
            have hn1_le : (n : ℝ) + 1 ≤ ↑(N₀ + n) + 1 := by
              push_cast; linarith [Nat.zero_le N₀]
            have han_le : a n τ ≤ 1 := (h_range n).2
            -- C(n)^2 >= 4*(N₀+n)^2 >= (n+1)*(N₀+n) >= a*(n+1)*(N₀+n)
            have hCn_sq : 4 * (↑(N₀ + n) : ℝ) ^ 2 ≤ C n τ ^ 2 := by nlinarith [hσ]
            -- a*(n+1)*(N₀+n) ≤ 1*(n+1)*(N₀+n) ≤ (N₀+n+1)*(N₀+n) ≤ 4*(N₀+n)^2 ≤ C(n)^2
            have h1 : a n τ * ((n : ℝ) + 1) * ↑(N₀ + n) ≤
                ((n : ℝ) + 1) * ↑(N₀ + n) := by
              have : 0 ≤ ((n : ℝ) + 1) * ↑(N₀ + n) := by positivity
              nlinarith [mul_le_mul_of_nonneg_right han_le this]
            have h2 : ((n : ℝ) + 1) * ↑(N₀ + n) ≤ (↑(N₀ + n) + 1) * ↑(N₀ + n) := by
              nlinarith
            have h3 : (↑(N₀ + n) + 1) * (↑(N₀ + n) : ℝ) ≤ 4 * (↑(N₀ + n) : ℝ) ^ 2 := by
              nlinarith [sq_nonneg (↑(N₀ + n) : ℝ)]
            linarith
          have h_il : a n τ * ((n : ℝ) + 1) / C n τ ≤ C n τ / ↑(N₀ + n) := by
            rw [div_le_div_iff₀ hCn hNn]; nlinarith [h_key]
          calc C n τ + a n τ * ((n : ℝ) + 1) / C n τ
              ≤ C n τ + C n τ / ↑(N₀ + n) := by linarith
            _ = C n τ * (1 + 1 / ↑(N₀ + n)) := by ring
            _ = C n τ * ((↑(N₀ + n) + 1) / ↑(N₀ + n)) := by
                congr 1; rw [add_div, div_self (ne_of_gt hNn)]
            _ ≤ (C 0 τ + 1 / C 0 τ + 2) * ↑(N₀ + n) * ((↑(N₀ + n) + 1) / ↑(N₀ + n)) :=
                mul_le_mul_of_nonneg_right ih (div_nonneg (by linarith) hNn.le)
            _ = (C 0 τ + 1 / C 0 τ + 2) * (↑(N₀ + n) + 1) := by
                rw [mul_assoc, mul_div_cancel₀ _ (ne_of_gt hNn)]
        · -- sigma < 2
          push_neg at hσ
          have h_il : a n τ * ((n : ℝ) + 1) / C n τ ≤ (↑(N₀ + n) + 1) / C 0 τ := by
            have hCn_ge : C 0 τ ≤ C n τ := hC_ge_C0 n
            have hn1_nn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
            have hn1_le : (n : ℝ) + 1 ≤ ↑(N₀ + n) + 1 := by
              push_cast; linarith [Nat.zero_le N₀]
            calc a n τ * ((n : ℝ) + 1) / C n τ
                ≤ ((n : ℝ) + 1) / C n τ := by
                  apply div_le_div_of_nonneg_right _ hCn.le
                  nlinarith [(h_range n).2, (h_range n).1]
              _ ≤ ((n : ℝ) + 1) / C 0 τ :=
                  div_le_div_of_nonneg_left hn1_nn hC0 hCn_ge
              _ ≤ (↑(N₀ + n) + 1) / C 0 τ :=
                  div_le_div_of_nonneg_right hn1_le hC0.le
          calc C n τ + a n τ * ((n : ℝ) + 1) / C n τ
              ≤ C n τ + (↑(N₀ + n) + 1) / C 0 τ := by linarith
            _ ≤ 2 * ↑(N₀ + n) + (↑(N₀ + n) + 1) / C 0 τ := by linarith [hσ]
            _ ≤ 2 * (↑(N₀ + n) + 1) + (↑(N₀ + n) + 1) / C 0 τ := by linarith
            _ = (↑(N₀ + n) + 1) * (2 + 1 / C 0 τ) := by ring
            _ ≤ (↑(N₀ + n) + 1) * (C 0 τ + 1 / C 0 τ + 2) := by
                apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
            _ = (C 0 τ + 1 / C 0 τ + 2) * (↑(N₀ + n) + 1) := by ring
  -- Use h_main to get the bound
  use C 0 τ + 1 / C 0 τ + 2; intro t
  by_cases hNt : N t τ = 0
  · simp only [hNt, Nat.cast_zero, div_zero]; positivity
  · rw [hN_grow t]
    have hNt_ge : 1 ≤ N₀ + t := by
      have : 0 < N t τ := Nat.pos_of_ne_zero hNt
      rw [hN_grow t] at this; omega
    have hNt_pos : (0 : ℝ) < ↑(N₀ + t) := Nat.cast_pos.mpr (by omega)
    rw [div_le_iff₀ hNt_pos]
    exact h_main t hNt_ge
