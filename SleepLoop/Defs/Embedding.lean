/-
  SleepLoop/Defs/Embedding.lean

  Definition: Embedding E : X -> R^d of a finite index set into Euclidean space,
  with bounded norm R = max_tau ||E(tau)||.
  Paper: §2.1 (setup paragraph before Definition 1).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset

/-! ## Embedding -/

/-- An embedding of a finite type X into ℝᵈ with bounded norm.
    Paper: §2.1 (setup paragraph). -/
structure Embedding (X : Type*) [Fintype X] (d : ℕ) where
  map : X → EuclideanSpace ℝ (Fin d)
  radius : ℝ
  radius_pos : 0 < radius
  bounded : ∀ τ, ‖map τ‖ ≤ radius

/-- The embedding radius R = max_τ ‖E(τ)‖.
    Paper: §2.1 (notation block). -/
noncomputable def Embedding.R {X : Type*} [Fintype X] {d : ℕ}
    (E : Embedding X d) : ℝ := E.radius
