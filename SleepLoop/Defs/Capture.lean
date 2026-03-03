/-
  SleepLoop/Defs/Capture.lean

  Definition: Step 5 (Capture).
  theta = max_{k in M} q * m_k,
  M_{t+1} = M_t union {E(tau) : q^T E(tau) > theta}.
  Paper: Definition 6 (def:capture), §2.1.
-/
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset

/-! ## Capture -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- The capture threshold: θ = max_{m ∈ M} q · m.
    Returns none when M is empty (convention: max ∅ = -∞).
    Paper: Definition 6 (def:capture). -/
noncomputable def captureThreshold
    (q : EuclideanSpace ℝ (Fin d))
    (M : Finset (EuclideanSpace ℝ (Fin d))) : WithBot ℝ :=
  M.sup (fun m => (edot q m : WithBot ℝ))

/-- Step 5: Capture. M_{t+1} = M_t ∪ {E(τ) : q·E(τ) > max_{k∈M} q·m_k}.
    When M = ∅, everything is captured (convention max ∅ = -∞).
    Paper: Definition 6 (def:capture). -/
noncomputable def captureStep [DecidableEq (EuclideanSpace ℝ (Fin d))]
    (E : Embedding X d) (q : EuclideanSpace ℝ (Fin d))
    (M : Finset (EuclideanSpace ℝ (Fin d))) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  if hM : M = ∅ then
    -- When M is empty, capture all embeddings
    M ∪ Finset.univ.image E.map
  else
    let θ := M.sup' (Finset.nonempty_of_ne_empty hM) (fun m => edot q m)
    M ∪ (Finset.univ.filter (fun τ => edot q (E.map τ) > θ)).image E.map
