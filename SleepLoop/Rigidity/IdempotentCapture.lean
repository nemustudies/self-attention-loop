/-
  SleepLoop/Rigidity/IdempotentCapture.lean

  Lemma (lem:idempotent): Idempotent capture.
  For a fixed query q and fixed M, capture applied twice yields
  the same result as capture applied once.
  Level: A.
-/
import SleepLoop.Defs.Capture

open Finset

/-! ## Idempotent Capture -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

omit [DecidableEq X] in
/-- After one capture pass, every admitted element e satisfies
    q . e > max_{k in M} q . m_k. Therefore the new threshold is at least
    as high, and a second capture pass admits nothing new.
    Paper: lem:idempotent. -/
theorem capture_idempotent [DecidableEq (EuclideanSpace ℝ (Fin d))]
    (E : Embedding X d) (q : EuclideanSpace ℝ (Fin d))
    (M : Finset (EuclideanSpace ℝ (Fin d))) :
    captureStep E q (captureStep E q M) = captureStep E q M := by
  -- Case split on whether M = ∅
  by_cases hM_empty : M = ∅
  · -- M = ∅: captureStep E q ∅ = ∅ ∪ univ.image E.map
    subst hM_empty
    -- First, simplify captureStep E q ∅
    have hcs_empty : captureStep E q ∅ =
        (∅ : Finset (EuclideanSpace ℝ (Fin d))) ∪ (univ : Finset X).image E.map := by
      unfold captureStep; rw [dif_pos rfl]
    rw [hcs_empty]
    set M₁ := (∅ : Finset (EuclideanSpace ℝ (Fin d))) ∪ (univ : Finset X).image E.map
    change captureStep E q M₁ = M₁
    by_cases h₁ : M₁ = ∅
    · -- h₁ : M₁ = ∅ where M₁ = ∅ ∪ univ.image E.map
      -- So univ.image E.map = ∅
      -- Goal: captureStep E q M₁ = M₁
      unfold captureStep; rw [dif_pos h₁]
      have h_img : (univ : Finset X).image E.map = ∅ := by
        have : (∅ : Finset (EuclideanSpace ℝ (Fin d))) ∪ (univ : Finset X).image E.map = ∅ := h₁
        simpa using this
      rw [h_img, Finset.union_empty]
    · -- M₁ nonempty, M₁ = univ.image E.map
      -- θ = M₁.sup'(...)(edot q ·) = max over all E.map τ of edot q (E.map τ)
      -- No E.map τ can exceed this max, so filter is empty
      set hne := Finset.nonempty_of_ne_empty h₁
      have hcs₁ : captureStep E q M₁ =
          M₁ ∪ ((univ : Finset X).filter (fun τ => edot q (E.map τ) >
            M₁.sup' hne (fun m => edot q m))).image E.map := by
        unfold captureStep; rw [dif_neg h₁]
      rw [hcs₁]
      suffices ∀ τ, ¬(edot q (E.map τ) > M₁.sup' hne (fun m => edot q m)) by
        have : (univ.filter fun τ => edot q (E.map τ) >
            M₁.sup' hne fun m => edot q m) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun τ _ => this τ)
        rw [this, Finset.image_empty, Finset.union_empty]
      intro τ; push_neg
      apply Finset.le_sup'
      exact Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · -- M ≠ ∅
    have hM_ne : M.Nonempty := Finset.nonempty_of_ne_empty hM_empty
    -- Unfold captureStep E q M
    have hcs : captureStep E q M =
        M ∪ ((univ : Finset X).filter (fun τ => edot q (E.map τ) >
          M.sup' hM_ne (fun m => edot q m))).image E.map := by
      unfold captureStep; rw [dif_neg hM_empty]
    -- Work with M' = captureStep E q M
    rw [hcs]
    -- Let θ = M.sup', S = captured, M' = M ∪ S
    set θ := M.sup' hM_ne (fun m => edot q m) with hθ_def
    set S := ((univ : Finset X).filter (fun τ => edot q (E.map τ) > θ)).image E.map
        with hS_def
    -- M' = M ∪ S is nonempty
    have hM'_ne : (M ∪ S) ≠ ∅ := Finset.Nonempty.ne_empty (hM_ne.mono Finset.subset_union_left)
    -- Need: captureStep E q (M ∪ S) = M ∪ S
    have hM'_ne' : (M ∪ S).Nonempty := hM_ne.mono Finset.subset_union_left
    -- Let θ' = (M ∪ S).sup'
    set θ' := (M ∪ S).sup' hM'_ne' (fun m => edot q m) with hθ'_def
    have hcs₂ : captureStep E q (M ∪ S) =
        (M ∪ S) ∪ ((univ : Finset X).filter (fun τ => edot q (E.map τ) > θ')).image E.map := by
      unfold captureStep; rw [dif_neg hM'_ne]
    rw [hcs₂]
    -- Show filter is empty: ∀ τ, edot q (E.map τ) ≤ θ'
    suffices h_all_le : ∀ τ, edot q (E.map τ) ≤ θ' by
      have : (univ.filter fun τ => edot q (E.map τ) > θ') = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun τ _ => not_lt.mpr (h_all_le τ))
      rw [this, Finset.image_empty, Finset.union_empty]
    intro τ
    by_cases hτ : edot q (E.map τ) > θ
    · -- E.map τ ∈ S ⊆ M ∪ S, so le_sup' gives edot q (E.map τ) ≤ θ'
      apply Finset.le_sup' (fun m => edot q m)
      exact Finset.mem_union_right M
        (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩))
    · -- edot q (E.map τ) ≤ θ ≤ θ' (since M ⊆ M ∪ S)
      push_neg at hτ
      calc edot q (E.map τ) ≤ θ := hτ
        _ ≤ θ' := Finset.sup'_mono (fun m => edot q m) (Finset.subset_union_left (s₂ := S)) hM_ne

/-- The threshold is non-decreasing under set enlargement:
    M subset M' implies max_{k in M} q . m_k <= max_{k in M'} q . m_k.
    Paper: lem:idempotent (threshold monotonicity). -/
theorem capture_threshold_mono
    (q : EuclideanSpace ℝ (Fin d))
    (M M' : Finset (EuclideanSpace ℝ (Fin d)))
    (hMM' : M ⊆ M')
    (hM : M.Nonempty) :
    M.sup' hM (fun m => edot q m) ≤
    M'.sup' (hM.mono hMM') (fun m => edot q m) := by
  exact Finset.sup'_mono (fun m => edot q m) hMM' hM
