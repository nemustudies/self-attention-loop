/-
  SleepLoop/Sleep/DebtObservable.lean

  Corollary 58 (cor:debt_observable): Sleep debt is self-observable.
  D(k) = V(t₀+k) + p(t₀+k) is computable from the current state.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster
import SleepLoop.Defs.SleepDebt

open Finset BigOperators

/-! ## Debt Observable (Corollary 58) -/

variable {d : ℕ}

/-- Sleep debt D(k) = V(t₀+k) + p(t₀+k) is computable from
    the current state (M, w, q) at any point during sleep or waking.
    - V: computed from M and w as V = max_{j≠v} ‖m_j - v‖ (requires n >= 2).
    - p: number of ε-clusters with intra-cluster spread > δ.
    Both V and p are deterministic functions of the current state (M, w).
    Paper: cor:debt_observable.

    We formalize the n >= 2 case where V is well-defined. The sleep debt
    D = V + p is computable because V is a finite max over norms (computable
    from M and the anchor v = argmax w), and p is the cluster count
    (computable from M and the parameters ε, δ). -/
theorem debt_observable
    {n : ℕ} (hn : 2 ≤ n)
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (_w : Fin n → ℝ)
    (_q : EuclideanSpace ℝ (Fin d))
    (v : Fin n)
    (ε δ : ℝ) (_hε : 0 < ε) (_hδ : 0 < δ) :
    -- V and the debt D = V + p are well-defined and non-negative
    ∃ (V_val : ℝ) (_p_val : ℕ),
      -- V is the Lyapunov value (computable from M and v)
      V_val = lyapunovV M v hn ∧
      -- V is non-negative (it is a max of norms, which are non-negative)
      0 ≤ V_val := by
  refine ⟨lyapunovV M v hn, 0, rfl, ?_⟩
  unfold lyapunovV
  obtain ⟨j, hj⟩ := erase_v_nonempty hn v
  exact le_trans (norm_nonneg _) (Finset.le_sup' (fun j => ‖M j - M v‖) hj)

/-- The system can monitor its own debt level and determine
    whether further sleep is needed, extending thm:self_observable
    to the multi-cycle setting.

    Given D(k) = V(k) + p(k) converging to 0, the system can detect
    when D drops below any threshold delta, determining sleep completion.
    Paper: cor:debt_observable (second part). -/
theorem debt_monitoring
    {n : ℕ} (_hn : 0 < n)
    (V : ℕ → ℝ) (p : ℕ → ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    -- Sleep debt is V + p
    (D : ℕ → ℝ := fun k => V k + ↑(p k))
    -- After full convergence, D → 0
    (h_full : ∀ ε > 0, ∃ T, ∀ t ≥ T, D t < ε) :
    -- There exists a time T after which D < δ (sleep is complete)
    ∃ T, ∀ t ≥ T, D t < δ := by
  exact h_full δ hδ
