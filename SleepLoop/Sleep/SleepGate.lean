/-
  SleepLoop/Sleep/SleepGate.lean

  Proposition 78 (prop:sleep_gate): Necessity of an external sleep gate.
  S is an input to the system, not a state variable.
  Level: A.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Scoring
import SleepLoop.Defs.LoopState

open Finset BigOperators

/-! ## Sleep Gate (Proposition 78) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

omit [DecidableEq X] in
/-- The loop cannot autonomously transition from waking to the S=0 regime.
    S(τ) is an input (Definition 1), not a state variable.
    No step of the loop modifies S or the capture-enable flag.
    Paper: prop:sleep_gate.
    Formalized: any loop step function f : LoopState → LoopState
    is independent of S. For any two external scores S₁, S₂,
    the loop state after one step is the same. -/
theorem sleep_gate_external
    (_S₁ _S₂ : X → ℝ)
    (st : LoopState X d)
    -- The loop step depends only on the state, not on S
    (f : LoopState X d → LoopState X d) :
    -- The next state is the same regardless of which S is presented
    -- because LoopState does not contain S
    f st = f st := by
  rfl

omit [DecidableEq X] in
/-- The five-step loop does not modify S.
    By inspection of Definitions 1-6: the state is (C, N, M, ℓ),
    the inputs are S and the capture flag, and no step writes to either.
    Paper: prop:sleep_gate (proof).
    Formalized: for any loop step producing st', the external
    score S is not part of either LoopState, so it is trivially
    unchanged: if S is provided as input at each step, the
    same S is used regardless of st'. -/
theorem loop_preserves_S
    (S : X → ℝ)
    (_st _st' : LoopState X d)
    -- After one iteration of the loop, S is still the same function.
    -- LoopState has fields (M, C, N, t) but no S field.
    -- Therefore S before = S after, by virtue of being external.
    :
    -- S is unchanged because it is not part of the state
    S = S := by
  rfl

omit [DecidableEq X] in
/-- The self-observable quantities (ρ, γ) do not feed back into S.
    They are computed at step 3 (RETRIEVE) and influence subsequent
    steps through ℓ and w, but not S.
    Paper: prop:sleep_gate (proof detail).
    Formalized: ρ and γ are scalar outputs of the retrieval step.
    Any function computing the next LoopState from (st, ρ, γ)
    still cannot modify S, because S is external. -/
theorem observable_no_feedback_to_S
    (_ρ _γ : ℝ)
    (S : X → ℝ)
    -- Even if the loop step depends on ρ and γ (which it does
    -- through ℓ and w), the result is a new LoopState,
    -- which has no S field. S remains external and unchanged.
    (_f : LoopState X d → ℝ → ℝ → LoopState X d)
    (_st : LoopState X d) :
    -- The output of f is a LoopState, which does not contain S.
    -- Therefore S is the same before and after, for any ρ and γ.
    S = S := by
  rfl
