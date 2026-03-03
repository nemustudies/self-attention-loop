/-
  SleepLoop/Sleep/Irreversibility.lean

  Corollary 43 (cor:irreversible): Irreversibility during waking.
  If |M_{t₂}| > |M_{t₁}|, then ρ(|M_{t₂}|) < ρ(|M_{t₁}|).
  No sequence of waking operations can restore ρ.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Sleep.MonotonePressure

open Finset BigOperators

/-! ## Irreversibility (Corollary 43) -/

variable {d : ℕ}

/-- Irreversibility during waking: if memory grows, retrieval precision
    strictly decreases and cannot be restored by any waking operation.
    Paper: cor:irreversible. -/
theorem irreversibility_during_waking
    (R : ℝ) (hR : 0 < R)
    (M_size : ℕ → ℕ)
    (t₁ t₂ : ℕ) (_ht : t₁ < t₂)
    (h_grew : M_size t₂ > M_size t₁)
    (h_pos : 1 < M_size t₁) :
    retrievalPrecisionBound (M_size t₂) R <
      retrievalPrecisionBound (M_size t₁) R := by
  exact monotone_pressure_rho_decreasing R hR (M_size t₁) (M_size t₂) h_grew h_pos

/-- No waking operation can restore ρ: for all t ≥ t₂,
    ρ(|M_t|) ≤ ρ(|M_{t₂}|) < ρ(|M_{t₁}|).
    Paper: cor:irreversible (second part). -/
theorem irreversibility_no_restoration
    (R : ℝ) (hR : 0 < R)
    (M_size : ℕ → ℕ)
    (h_nondec : ∀ t, M_size t ≤ M_size (t + 1))
    (t₁ t₂ : ℕ) (_ht : t₁ < t₂)
    (h_grew : M_size t₂ > M_size t₁)
    (h_pos : 1 < M_size t₁) :
    ∀ t ≥ t₂, retrievalPrecisionBound (M_size t) R ≤
      retrievalPrecisionBound (M_size t₂) R := by
  intro t ht_ge
  have h_mono := monotone_pressure_M_nondecreasing M_size h_nondec t₂ t ht_ge
  have h_pos_t₂ : 1 < M_size t₂ := by omega
  rcases h_mono.eq_or_lt with h_eq | h_lt
  · exact le_of_eq (by rw [h_eq])
  · exact le_of_lt (monotone_pressure_rho_decreasing R hR (M_size t₂) (M_size t) h_lt h_pos_t₂)
