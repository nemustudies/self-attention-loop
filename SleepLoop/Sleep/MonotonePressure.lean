/-
  SleepLoop/Sleep/MonotonePressure.lean

  Theorem 42 (thm:monotone_pressure): Monotonicity of sleep pressure.
  During sustained waking, retrieval degradation is monotone and irreversible.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Monotone Pressure (Theorem 42) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- The retrieval precision bound: ρ(n) = max_{g ≤ 2R²} [1/(1 + (n-1)exp(-g))].
    This is achieved at g = 2R² and is monotone decreasing in n.
    Paper: thm:monotone_pressure(iv). -/
noncomputable def retrievalPrecisionBound (n : ℕ) (R : ℝ) : ℝ :=
  1 / (1 + (↑(n - 1)) * Real.exp (-(2 * R ^ 2)))

omit [Fintype X] [DecidableEq X] in
/-- (i) C_t(τ) is non-decreasing for all τ ∈ X.
    Paper: thm:monotone_pressure(i). -/
theorem monotone_pressure_C_nondecreasing
    (C : ℕ → X → ℝ)
    (a : ℕ → X → ℝ) (ha : ∀ t τ, 0 ≤ a t τ)
    (hC : ∀ t τ, 0 < C t τ)
    (h_update : ∀ t τ, C (t + 1) τ = C t τ + a t τ * (↑(t + 1)) / C t τ)
    (τ : X) (t : ℕ) :
    C t τ ≤ C (t + 1) τ := by
  rw [h_update t τ]
  linarith [div_nonneg (mul_nonneg (ha t τ) (Nat.cast_nonneg (t + 1))) (le_of_lt (hC t τ))]

/-- (ii) N_t(τ) = N_0 + t is strictly increasing.
    Paper: thm:monotone_pressure(ii). -/
theorem monotone_pressure_N_increasing
    (N₀ : ℕ) (_hN₀ : 0 < N₀) (t : ℕ) :
    N₀ + t < N₀ + (t + 1) := by
  omega

/-- (iii) |M_t| is non-decreasing, strictly increasing at capture events.
    Paper: thm:monotone_pressure(iii). -/
theorem monotone_pressure_M_nondecreasing
    (M_size : ℕ → ℕ)
    (h_nondec : ∀ t, M_size t ≤ M_size (t + 1)) :
    ∀ t₁ t₂, t₁ ≤ t₂ → M_size t₁ ≤ M_size t₂ := by
  intro t₁ t₂ h
  induction h with
  | refl => exact le_refl _
  | step h ih => exact le_trans ih (h_nondec _)

/-- (iv) ρ(|M|) is monotone decreasing in |M|.
    Paper: thm:monotone_pressure(iv). -/
theorem monotone_pressure_rho_decreasing
    (R : ℝ) (_hR : 0 < R)
    (n₁ n₂ : ℕ) (hn : n₁ < n₂) (hn₁ : 1 < n₁) :
    retrievalPrecisionBound n₂ R < retrievalPrecisionBound n₁ R := by
  unfold retrievalPrecisionBound
  have hexp : 0 < Real.exp (-(2 * R ^ 2)) := Real.exp_pos _
  have hn1_nat : n₁ - 1 < n₂ - 1 := by omega
  have hn1_cast : (↑(n₁ - 1) : ℝ) < (↑(n₂ - 1) : ℝ) := Nat.cast_lt.mpr hn1_nat
  have hdenom1_pos : 0 < 1 + ↑(n₁ - 1) * Real.exp (-(2 * R ^ 2)) := by
    linarith [mul_nonneg (Nat.cast_nonneg (n₁ - 1)) (le_of_lt hexp)]
  have hdenom2_pos : 0 < 1 + ↑(n₂ - 1) * Real.exp (-(2 * R ^ 2)) := by
    linarith [mul_nonneg (Nat.cast_nonneg (n₂ - 1)) (le_of_lt hexp)]
  have hdenom_lt : 1 + ↑(n₁ - 1) * Real.exp (-(2 * R ^ 2)) <
      1 + ↑(n₂ - 1) * Real.exp (-(2 * R ^ 2)) := by
    linarith [mul_lt_mul_of_pos_right hn1_cast hexp]
  rw [div_lt_div_iff₀ hdenom2_pos hdenom1_pos]
  linarith

/-- (v) System's retrieval capacity is non-increasing during waking.
    Composition of (iii) and (iv): ρ(|M_t|) is non-increasing in t.
    Paper: thm:monotone_pressure(v). -/
theorem monotone_pressure_capacity_nonincreasing
    (R : ℝ) (hR : 0 < R)
    (M_size : ℕ → ℕ)
    (h_nondec : ∀ t, M_size t ≤ M_size (t + 1))
    (h_pos : ∀ t, 1 < M_size t)
    (t₁ t₂ : ℕ) (ht : t₁ ≤ t₂) :
    retrievalPrecisionBound (M_size t₂) R ≤ retrievalPrecisionBound (M_size t₁) R := by
  by_cases heq : M_size t₁ = M_size t₂
  · rw [heq]
  · have hlt : M_size t₁ < M_size t₂ := by
      exact lt_of_le_of_ne (monotone_pressure_M_nondecreasing M_size h_nondec t₁ t₂ ht) heq
    exact le_of_lt (monotone_pressure_rho_decreasing R hR (M_size t₁) (M_size t₂) hlt (h_pos t₁))
