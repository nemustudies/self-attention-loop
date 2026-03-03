/-
  SleepLoop/Defs/Retrieval.lean

  Definition: Step 3 (Retrieval).
  q = aE (query), w = phi(q * M^T) (retrieval weights),
  ell = wM (retrieved impression), b = EK*ell (feedback bias).
  Paper: Definition 4 (def:retrieval), §2.1.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.LoopState
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators

/-! ## Retrieval -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- Dot product between two vectors in EuclideanSpace ℝ (Fin d). -/
noncomputable abbrev edot {d : ℕ}
    (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  @inner ℝ (EuclideanSpace ℝ (Fin d)) _ u v

/-- The query vector: q = aE = Σ_τ a(τ) · E(τ).
    Paper: q = aE (Definition 4, line 1). -/
noncomputable def queryVector
    (E : Embedding X d) (a : X → ℝ) : EuclideanSpace ℝ (Fin d) :=
  ∑ τ : X, a τ • E.map τ

/-- Retrieval weights: w = φ(qMᵀ).
    Returns weights indexed over Fin n (the memory is given as a function Fin n → ℝᵈ).
    Paper: w = φ(q·Mᵀ) (Definition 4, line 2). -/
noncomputable def retrievalWeights
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  φ (fun j => edot q (M j))

/-- Retrieved impression: ℓ = wM = Σ_j w_j · m_j.
    Paper: ℓ(q, M) = wM (Definition 4, line 3). -/
noncomputable def retrievedImpression
    {n : ℕ} (w : Fin n → ℝ) (M : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ j : Fin n, w j • M j

/-- Feedback bias: b(τ) = E(τ) · K · ℓ.
    Paper: b = EKℓ (Definition 4, line 4). -/
noncomputable def feedbackBias
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ell : EuclideanSpace ℝ (Fin d)) (τ : X) : ℝ :=
  edot (E.map τ) (K ell)

/-- The full retrieval output. -/
structure RetrievalOutput (X : Type*) [Fintype X] (d n : ℕ) where
  q : EuclideanSpace ℝ (Fin d)
  w : Fin n → ℝ
  ell : EuclideanSpace ℝ (Fin d)
  b : X → ℝ
