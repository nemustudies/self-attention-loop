/-
  SleepLoop/Core/ForgettingCurve.lean

  Forgetting curve: if attention to an element ceases at time T
  (a_t(τ) = 0 for all t ≥ T), then C stays constant at C_T and
  salience σ_t(τ) = C_T / (N_0 + t) decays hyperbolically.
  Level: A.
-/
import SleepLoop.Defs.Accumulation
import SleepLoop.Defs.LoopState

/-! ## Forgetting Curve -/

variable {X : Type*}

/-- If attention ceases at time T, then the cumulative attention C is constant
    for all t >= T. The key insight: when a = 0, the accumulation increment
    a * (t+1) / C = 0 * (t+1) / C = 0, so C_{t+1} = C_t. -/
theorem accumulateC_constant_when_attention_zero
    (C : ℕ → X → ℝ) (a : ℕ → X → ℝ) (τ : X) (T : ℕ)
    (h_update_C : ∀ t, C (t + 1) τ = accumulateC (C t) (a t) t τ)
    (h_cease : ∀ t, T ≤ t → a t τ = 0) :
    ∀ t, T ≤ t → C t τ = C T τ := by
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

/-- Forgetting curve (hyperbolic decay): if attention ceases at time T,
    then for t >= T the salience is sigma_t(tau) = C_T(tau) / (N_0(tau) + t),
    which decays hyperbolically in t. -/
theorem forgetting_curve_hyperbolic
    (C : ℕ → X → ℝ) (N : ℕ → X → ℕ) (a : ℕ → X → ℝ)
    (τ : X) (T : ℕ)
    (h_update_C : ∀ t, C (t + 1) τ = accumulateC (C t) (a t) t τ)
    (h_update_N : ∀ t, N (t + 1) τ = N t τ + 1)
    (h_cease : ∀ t, T ≤ t → a t τ = 0) :
    ∀ t, T ≤ t → C t τ / (N t τ : ℝ) = C T τ / (N 0 τ + t : ℝ) := by
  intro t ht
  -- Step 1: C is constant after T
  have hC_const := accumulateC_constant_when_attention_zero C a τ T h_update_C h_cease t ht
  -- Step 2: N grows linearly
  have hN_grow : ∀ s, N s τ = N 0 τ + s := by
    intro s
    induction s with
    | zero => simp
    | succ m ih => rw [h_update_N m, ih]; omega
  -- Step 3: Combine
  rw [hC_const, hN_grow t, Nat.cast_add]
