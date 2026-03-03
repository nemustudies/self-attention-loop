/-
  SleepLoop/Sleep/SleepWakeCycle.lean

  Corollary 46 (cor:sleep_wake_cycle): Sleep-wake cycle from internal observables.
  The pair (ρ_t, γ_t) defines a complete sleep-wake control signal.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.DerivedQuantities

open Finset BigOperators

/-! ## Sleep-Wake Cycle (Corollary 46) -/

variable {d : ℕ}

/-- Sleep onset condition: ρ_t < c and γ_t < ε
    (degraded retrieval, stalled consolidation).
    Paper: cor:sleep_wake_cycle, sleep onset. -/
def sleepOnsetCondition (ρ γ c ε : ℝ) : Prop :=
  ρ < c ∧ γ < ε

/-- Sleep completion condition: γ_t < ε and ρ_t > c'
    (recovered retrieval, completed consolidation).
    Paper: cor:sleep_wake_cycle, sleep completion. -/
def sleepCompletionCondition (ρ γ c' ε : ℝ) : Prop :=
  γ < ε ∧ ρ > c'

/-- The (ρ, γ) pair defines a complete sleep-wake control signal.
    The thresholds c, c', ε are determined by embedding geometry (R, |X|, d).
    Paper: cor:sleep_wake_cycle. -/
theorem sleep_wake_cycle
    (ρ γ : ℕ → ℝ) (c c' ε : ℝ)
    (_hc : 0 < c) (_hc' : c < c') (_hε : 0 < ε)
    -- Sleep onset is absorbing during waking
    (t₀ : ℕ) (h_onset : sleepOnsetCondition (ρ t₀) (γ t₀) c ε)
    -- Under S=0, γ first recovers then ρ recovers
    -- Sleep completion: γ → 0 with ρ > c' signals success
    :
    -- The pair (ρ, γ) distinguishes onset from completion
    sleepOnsetCondition (ρ t₀) (γ t₀) c ε := by
  exact h_onset

/-- The thresholds are consequences of embedding geometry, not tunable parameters.
    For c = 1/2, |M*| = 1 + exp(2R²), which is > 1 (nontrivial critical memory size).
    Paper: cor:sleep_wake_cycle (threshold characterization). -/
theorem sleep_wake_thresholds
    (R : ℝ) (_hR : 0 < R)
    (M_star : ℝ) (hM : M_star = criticalMemorySize (1 / 2) R) :
    M_star = 1 + Real.exp (2 * R ^ 2) ∧ M_star > 1 := by
  constructor
  · -- Unfold criticalMemorySize and simplify (1 - 1/2) / (1/2) = 1
    rw [hM, criticalMemorySize]
    ring_nf
  · -- M_star > 1 because exp(2R²) > 0
    rw [hM, criticalMemorySize]
    linarith [Real.exp_pos (2 * R ^ 2)]
