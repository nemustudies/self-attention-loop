/-
  SleepLoop/Core/FiniteMemory.lean

  Lemma 6 (lem:finite): Finite memory without consolidation.
  If consolidation is disabled (lambda = 0), then |M_t| <= |X| for all t.
  By pigeonhole: each E(tau) enters at most once.
  Level: 𝒜.
-/
import SleepLoop.Defs.Capture
import SleepLoop.Core.ConvexHullInvariance

/-! ## Finite Memory -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
  [DecidableEq (EuclideanSpace ℝ (Fin d))]

omit [DecidableEq X] [DecidableEq (EuclideanSpace ℝ (Fin d))] in
/-- lem:finite: If consolidation is disabled, |M_t| ≤ |X| for all t.
    Without consolidation, M contains only vectors of the form E(τ).
    Each element enters at most once (pigeonhole). -/
theorem finite_memory_without_consolidation
    (E : Embedding X d)
    (M : Finset (EuclideanSpace ℝ (Fin d)))
    (hM : ∀ m ∈ M, ∃ τ : X, m = E.map τ) :
    M.card ≤ Fintype.card X := by
  -- Every element of M is in the image of E.map over Finset.univ
  have hM_sub : M ⊆ Finset.univ.image E.map := by
    intro m hm
    obtain ⟨τ, hτ⟩ := hM m hm
    exact Finset.mem_image.mpr ⟨τ, Finset.mem_univ τ, hτ.symm⟩
  calc M.card
      ≤ (Finset.univ.image E.map).card := Finset.card_le_card hM_sub
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card X := Finset.card_univ
