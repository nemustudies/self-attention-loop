/-
  SleepLoop/Defs/SleepDebt.lean

  Definition: Sleep debt (residual Lyapunov value) and nap structure.
  Paper: Definition 55 (def:sleep_debt), §3.7;
         Definition 89 (def:nap), Appendix B.4.
-/
import SleepLoop.Defs.DerivedQuantities

/-! ## Sleep Debt -/

variable {d : ℕ}

/-- Sleep debt: the residual Lyapunov value V_res after truncated consolidation.
    Paper: Definition 55 (def:sleep_debt). -/
noncomputable def sleepDebt
    {n : ℕ} (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) (V_target : ℝ) : ℝ :=
  lyapunovV M v hn - V_target

/-- A nap: a consolidation episode of duration T_nap < T_full.
    Paper: Definition 89 (def:nap). -/
structure Nap where
  duration : ℕ
  full_duration : ℕ
  truncated : duration < full_duration
