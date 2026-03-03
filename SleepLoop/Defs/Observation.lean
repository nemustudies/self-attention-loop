/-
  SleepLoop/Defs/Observation.lean

  Definition: Step 1 (Observation). a = phi(S') in [0,1]^|X|.
  Paper: Definition 2 (def:observation), §2.1.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Scoring

open Finset BigOperators

/-! ## Observation -/

/-- Step 1: Observation.
    a = φ(S + σ + b) ∈ [0,1]^|X|.
    Paper: Definition 2 (def:observation). -/
noncomputable def observe {n : ℕ}
    (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (S σ b : Fin n → ℝ) : Fin n → ℝ :=
  φ (fun i => S i + σ i + b i)

/-- The observation vector lies on the simplex. -/
theorem observe_on_simplex {n : ℕ}
    {φ : (Fin n → ℝ) → (Fin n → ℝ)} [SimplexMap φ]
    (S σ b : Fin n → ℝ) :
    (∀ i, 0 ≤ observe φ S σ b i) ∧ ∑ i : Fin n, observe φ S σ b i = 1 := by
  unfold observe
  exact ⟨fun i => SimplexMap.nonneg _ i, SimplexMap.sum_one _⟩
