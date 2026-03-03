/-
  SleepLoop/Defs/Accumulation.lean

  Definition: Step 2 (Accumulation).
  C_{t+1}(tau) = C_t(tau) + a_t(tau) * (t+1) / C_t(tau),
  N_{t+1}(tau) = N_t(tau) + 1, sigma_{t+1}(tau) = C_{t+1}(tau) / N_{t+1}(tau).
  Paper: Definition 3 (def:accumulation), §2.1.
-/
import SleepLoop.Defs.LoopState

/-! ## Accumulation -/

/-- Step 2: Accumulation update for the cumulative attention C.
    C_{t+1}(τ) = C_t(τ) + a_t(τ) · (t+1) / C_t(τ).
    Paper: Definition 3 (def:accumulation). -/
noncomputable def accumulateC {X : Type*}
    (C : X → ℝ) (a : X → ℝ) (t : ℕ) (τ : X) : ℝ :=
  C τ + a τ * ((t : ℝ) + 1) / C τ

/-- Step 2: Lifetime counter update. N_{t+1}(τ) = N_t(τ) + 1.
    Paper: Definition 3 (def:accumulation). -/
def accumulateN {X : Type*} (N : X → ℕ) (τ : X) : ℕ :=
  N τ + 1

/-- The accumulation update preserves positivity of C. -/
theorem accumulateC_pos {X : Type*}
    (C : X → ℝ) (a : X → ℝ) (t : ℕ) (τ : X)
    (hC : 0 < C τ) (ha : 0 ≤ a τ) :
    0 < accumulateC C a t τ := by
  unfold accumulateC
  have h1 : (0 : ℝ) ≤ a τ * (↑t + 1) / C τ := by
    apply div_nonneg
    · exact mul_nonneg ha (by positivity)
    · exact le_of_lt hC
  linarith
