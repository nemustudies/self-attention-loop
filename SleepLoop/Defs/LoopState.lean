/-
  SleepLoop/Defs/LoopState.lean

  Definition: The full state of the self-referring attention loop at time t.
  Memory M is a Finset of vectors in R^d; C is cumulative attention; N is lifetime counter.
  Paper: §2.1 (initial conditions M_0 = empty, C_0 > 0, N_0 = 1).
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import SleepLoop.Defs.Embedding

/-! ## Loop State -/

/-- The full state of the self-referring attention loop.
    Paper: §2.1 (initial conditions). -/
structure LoopState (X : Type*) [Fintype X] (d : ℕ) where
  /-- Memory: a finite set of vectors (impressions) in ℝᵈ. -/
  M : Finset (EuclideanSpace ℝ (Fin d))
  /-- Cumulative attention per element. C₀(τ) > 0. -/
  C : X → ℝ
  /-- Lifetime counter per element. N₀(τ) ≥ 1. -/
  N : X → ℕ
  /-- Step index. -/
  t : ℕ
  /-- C is always positive. -/
  C_pos : ∀ τ, 0 < C τ
  /-- N is always positive. -/
  N_pos : ∀ τ, 0 < N τ

/-- Salience: σ(τ) = C(τ) / N(τ).
    Paper: Definition 3 (def:accumulation), third line. -/
noncomputable def LoopState.sigma {X : Type*} [Fintype X] {d : ℕ}
    (st : LoopState X d) (τ : X) : ℝ :=
  st.C τ / (st.N τ : ℝ)

/-- Initial loop state: M₀ = ∅, C₀ > 0, N₀ = 1.
    Paper: §2.1 (setup paragraph). -/
noncomputable def LoopState.init {X : Type*} [Fintype X] {d : ℕ}
    (C₀ : X → ℝ) (hC₀ : ∀ τ, 0 < C₀ τ) : LoopState X d where
  M := ∅
  C := C₀
  N := fun _ => 1
  t := 0
  C_pos := hC₀
  N_pos := fun _ => Nat.one_pos
