/-
  SleepLoop/Core/MonotoneAcquisition.lean

  Corollary 4 (cor:acquisition): Monotone acquisition.
  |M| is non-decreasing: capture adds elements by union
  and no operation removes them.
  Level: 𝒜.
-/
import SleepLoop.Defs.Capture
import Mathlib.Data.Finset.Card

/-! ## Monotone Acquisition -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
  [DecidableEq (EuclideanSpace ℝ (Fin d))]

omit [DecidableEq X] in
/-- cor:acquisition: |M| is non-decreasing after a capture step.
    Capture adds elements by union, so |M_{t+1}| ≥ |M_t|. -/
theorem capture_card_nondecreasing
    (E : Embedding X d)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Finset (EuclideanSpace ℝ (Fin d))) :
    M.card ≤ (captureStep E q M).card := by
  unfold captureStep
  split
  · -- Case M = ∅: captureStep = M ∪ Finset.univ.image E.map
    exact Finset.card_le_card Finset.subset_union_left
  · -- Case M ≠ ∅: captureStep = M ∪ (filter ...).image E.map
    exact Finset.card_le_card Finset.subset_union_left

/-- cor:acquisition (part 2): The capture threshold is non-decreasing in |M|.
    Adding elements can only increase or maintain the maximum. -/
theorem capture_threshold_monotone
    (q : EuclideanSpace ℝ (Fin d))
    (M : Finset (EuclideanSpace ℝ (Fin d)))
    (m_new : EuclideanSpace ℝ (Fin d)) :
    captureThreshold q M ≤ captureThreshold q (M ∪ {m_new}) := by
  unfold captureThreshold
  exact Finset.sup_mono Finset.subset_union_left
