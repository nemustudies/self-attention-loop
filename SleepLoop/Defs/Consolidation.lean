/-
  SleepLoop/Defs/Consolidation.lean

  Definition: Step 4 (Consolidation).
  lambda_j = lambda(w_j / max_k w_k), T_j = phi((m_j + q) * M^T) * M,
  m_j' = (1 - lambda_j) * m_j + lambda_j * T_j.
  Paper: Definition 5 (def:consolidation), §2.1.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.BlendRate
import SleepLoop.Defs.Retrieval
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators

/-! ## Consolidation -/

variable {d : ℕ}

/-- The consolidation target for impression j:
    T_j = phi((m_j + q) . M^T) . M = sum_k alpha_k^(j) . m_k
    where alpha^(j) = phi((m_j + q) . M^T).
    Paper: Definition 5 (def:consolidation), line 2. -/
noncomputable def consolidationTarget
    {n : ℕ} (phi : (Fin n → ℝ) → (Fin n → ℝ))
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (j : Fin n) : EuclideanSpace ℝ (Fin d) :=
  let scores : Fin n → ℝ := fun k => edot (M j + q) (M k)
  let alpha := phi scores
  ∑ k : Fin n, alpha k • M k

/-- The consolidation blend rates: blend_j = br(w_j / max_k w_k).
    Paper: Definition 5 (def:consolidation), line 1. -/
noncomputable def consolidationBlendRates
    {n : ℕ} (br : BlendRate) (w : Fin n → ℝ)
    (hM : 0 < n) : Fin n → ℝ :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hM⟩⟩
  let w_max := Finset.sup' Finset.univ Finset.univ_nonempty w
  fun j => br.fn (w j / w_max)

/-- The consolidation update: m_j' = (1 - blend_j) . m_j + blend_j . T_j.
    Paper: Definition 5 (def:consolidation), line 3. -/
noncomputable def consolidationStep
    {n : ℕ} (phi : (Fin n → ℝ) → (Fin n → ℝ))
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hM : 0 < n) : Fin n → EuclideanSpace ℝ (Fin d) :=
  let rates := consolidationBlendRates br w hM
  fun j =>
    let T_j := consolidationTarget phi q M j
    (1 - rates j) • M j + rates j • T_j

/-- The anchor: v = argmax_k w_k (most-retrieved impression).
    Paper: §2.1 (notation block). -/
noncomputable def anchor {n : ℕ}
    (w : Fin n → ℝ) (hn : 0 < n) : Fin n :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  (Finset.exists_max_image Finset.univ w Finset.univ_nonempty).choose
