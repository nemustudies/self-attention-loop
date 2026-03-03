/-
  SleepLoop/Core/HistoryIndependence.lean

  Corollary 1 (cor:N_history_independent): History-independence of lifetime counter.
  N_t(tau) = N_0 + t for all tau, t. The lifetime counter is independent
  of the attention history.
  Level: 𝒜.
-/
import SleepLoop.Defs.Accumulation

/-! ## History-Independence of the Lifetime Counter -/

/-- cor:N_history_independent: For every τ and every t ≥ 0,
    N_t(τ) = N_0 + t. The denominator of σ = C/N is independent
    of the attention history {a_s(τ)}_{s < t}. -/
theorem lifetime_counter_history_independent {X : Type*}
    (N₀ : X → ℕ) (τ : X) (t : ℕ) :
    -- After t applications of accumulateN starting from N₀,
    -- the result is N₀(τ) + t.
    Nat.iterate (fun N => accumulateN N) t N₀ τ = N₀ τ + t := by
  induction t generalizing N₀ with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.iterate, ih, accumulateN]
    omega
