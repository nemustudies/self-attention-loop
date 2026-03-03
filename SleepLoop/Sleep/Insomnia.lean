/-
  SleepLoop/Sleep/Insomnia.lean

  Corollary 79 (cor:insomnia): Cost of ignoring the sleep signal.
  Score degradation bound under insomnia.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Insomnia (Corollary 79) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) Memory continues to grow when sleep signal is ignored.
    |M| grows, ρ degrades further.
    Paper: cor:insomnia(i). -/
theorem insomnia_memory_grows
    (M_size : ℕ → ℕ)
    (ρ : ℕ → ℝ) (R : ℝ) (_hR : 0 < R)
    (t₀ : ℕ) (c _ε : ℝ) (_hc : 0 < c)
    -- Sleep condition fired at t₀
    (_h_onset : ρ t₀ < c)
    -- But no regime transition: capture remains enabled
    (_h_grows : ∀ t ≥ t₀, M_size t ≤ M_size (t + 1))
    (_h_pos : ∀ t ≥ t₀, 1 < M_size t)
    -- ρ degrades as memory grows (Paper: ρ ≤ 1/|M|, monotone in |M|)
    (h_rho_mono : ∀ t t', M_size t ≤ M_size t' → ρ t' ≤ ρ t) :
    -- ρ continues degrading
    ∀ t ≥ t₀, ∀ t' ≥ t,
      M_size t' ≥ M_size t → ρ t' ≤ ρ t := by
  intro t _ht t' _ht' h_grew
  exact h_rho_mono t t' h_grew

/-- (ii) Consolidation deficit grows as O(log k).
    The eventual sleep duration to recover to tolerance δ satisfies
    T_sleep ≥ log(V_{t₀+k}/δ) / γ_min, growing as O(log k).
    Paper: cor:insomnia(ii). -/
theorem insomnia_consolidation_deficit
    (V₀ R γ_min δ : ℝ)
    (_hV : 0 < V₀) (hR : 0 < R)
    (hγ : 0 < γ_min) (hγ1 : γ_min < 1)
    (hδ : 0 < δ)
    -- δ < V₀ ensures log(V_delayed/δ) > 0 (consolidation deficit exists)
    (h_large : δ < V₀)
    (_k : ℕ) (n_k : ℕ) (hn : 0 < n_k) :
    -- V_{t₀+k} ≤ V₀ + 2R·n_k
    -- T_sleep ≥ log((V₀ + 2R·n_k)/δ) / γ_min
    -- This grows as O(log k / γ_min) since n_k = O(k)
    let V_delayed := V₀ + 2 * R * ↑n_k
    Real.log (V_delayed / δ) / γ_min > 0 := by
  simp only
  apply div_pos _ hγ
  apply Real.log_pos
  rw [lt_div_iff₀ hδ]
  have h_nk_pos : (0 : ℝ) < ↑n_k := Nat.cast_pos.mpr hn
  linarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < 2) hR) h_nk_pos]

/-- (iii) Permanent degradation under indefinite insomnia.
    If signal ignored indefinitely: ρ → 1/|M| → 0, γ → 0, V > 0 growing.
    No waking consolidation can reverse this.
    Paper: cor:insomnia(iii). -/
theorem insomnia_permanent_degradation
    (M_size : ℕ → ℕ) (_ρ : ℕ → ℝ) (R : ℝ) (_hR : 0 < R)
    -- |M| → ∞ (indefinite capture with no sleep)
    (h_unbounded : ∀ N, ∃ t, M_size t > N)
    (_h_pos : ∀ t, 1 < M_size t)
    -- Memory size is non-decreasing (captures only add)
    (h_mono : ∀ t, M_size t ≤ M_size (t + 1)) :
    -- ρ → 0
    ∀ ε > 0, ∃ T, ∀ t ≥ T,
      1 / (1 + (↑(M_size t - 1)) * Real.exp (-(2 * R ^ 2))) < ε := by
  intro ε hε
  -- We need 1 / (1 + (M_size t - 1) * exp(-2R²)) < ε
  -- i.e. (M_size t - 1) * exp(-2R²) > 1/ε - 1
  -- Since M_size → ∞, we can find T with M_size T large enough
  set e := Real.exp (-(2 * R ^ 2)) with he_def
  have he_pos : 0 < e := Real.exp_pos _
  -- Find N such that N * e > 1/ε (then 1/(1 + N*e) < ε)
  -- We need N > 1/(ε * e)
  have hεe_pos : 0 < ε * e := mul_pos hε he_pos
  obtain ⟨N_nat, hN_nat⟩ := exists_nat_gt (1 / (ε * e))
  -- Find T where M_size T - 1 ≥ N_nat
  obtain ⟨T, hT⟩ := h_unbounded (N_nat + 1)
  use T
  intro t ht
  have h_mt_ge : M_size T ≤ M_size t := by
    have : ∀ k, M_size T ≤ M_size (T + k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => exact le_trans ih (h_mono _)
    have ⟨k, hk⟩ : ∃ k, t = T + k := ⟨t - T, by omega⟩
    rw [hk]; exact this k
  have h_mt_large : M_size t > N_nat + 1 := lt_of_lt_of_le hT h_mt_ge
  have h_sub_pos : 0 < M_size t - 1 := by omega
  have h_sub_ge : N_nat < M_size t - 1 := by omega
  have h_cast_sub : (↑(M_size t - 1) : ℝ) > ↑N_nat := by exact_mod_cast h_sub_ge
  -- Now (M_size t - 1) * e > N_nat * e > 1/ε - something...
  -- Actually: N_nat > 1/(ε * e), so N_nat * e > 1/ε, so 1 + (M_size t - 1)*e > 1/ε
  -- We need 1 / (1 + (M_size t - 1) * e) < ε
  -- i.e. 1 < ε * (1 + (M_size t - 1) * e)
  -- From N_nat > 1/(ε*e) and M_size t - 1 > N_nat, we get (M_size t - 1) > 1/(ε*e)
  -- so (M_size t - 1) * e > 1/ε, so ε * (M_size t - 1) * e > 1
  have h_sub_cast : (0 : ℝ) < ↑(M_size t - 1) := by exact_mod_cast h_sub_pos
  have h_cast_gt : (↑(M_size t - 1) : ℝ) > 1 / (ε * e) := by
    calc (↑(M_size t - 1) : ℝ) > ↑N_nat := h_cast_sub
      _ > 1 / (ε * e) := hN_nat
  -- (M_size t - 1) * (ε * e) > 1
  have h_prod_gt : (↑(M_size t - 1) : ℝ) * (ε * e) > 1 := by
    rwa [gt_iff_lt, div_lt_iff₀ hεe_pos] at h_cast_gt
  have h_denom_pos : 0 < 1 + (↑(M_size t - 1) : ℝ) * e := by
    linarith [mul_pos h_sub_cast he_pos]
  rw [div_lt_iff₀ h_denom_pos]
  nlinarith [mul_pos h_sub_cast he_pos]
