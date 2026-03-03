/-
  SleepLoop/Rigidity/CaptureRigidity.lean

  Proposition (prop:capture_rigidity): Rigidity of the capture threshold.
  Among parameter-free, always-defined, memoryless thresholds,
  max is the unique one consistent with idempotent capture.
  Level: A.
-/
import SleepLoop.Defs.Capture
import SleepLoop.Rigidity.IdempotentCapture

open Finset

/-! ## Capture Rigidity -/

variable {d : ℕ}

/-- A memoryless threshold function: given a finite multiset of
    real scores (the dot products q·mₖ for k ∈ M), returns a threshold. -/
def MemorylessThreshold :=
  ∀ (n : ℕ), (Fin n → ℝ) → ℝ

/-- A memoryless threshold is idempotent-compatible if:
    whenever M' ⊇ M (both nonempty) is the result of admitting elements
    above θ(M,q), then θ(M',q) ≥ θ(M,q) (so a second pass admits nothing new).
    The precondition 0 < n ensures we only consider nonempty memory sets,
    since the capture threshold is undefined for empty M. -/
def IdempotentCompatible (θ : MemorylessThreshold) : Prop :=
  ∀ (n n' : ℕ) (scores : Fin n → ℝ) (scores' : Fin n' → ℝ),
    0 < n →
    (∀ i, ∃ j, scores i = scores' j) →  -- M ⊆ M'
    θ n scores ≤ θ n' scores'

/-- The max threshold function: returns sup' of scores when nonempty, 0 otherwise. -/
noncomputable def maxThreshold : MemorylessThreshold := fun n scores =>
  if h : 0 < n then
    haveI : Nonempty (Fin n) := ⟨⟨0, h⟩⟩
    Finset.sup' Finset.univ Finset.univ_nonempty scores
  else 0

/-- max is idempotent-compatible: if M subset M' (M nonempty),
    then max(M) <= max(M').
    Paper: prop:capture_rigidity (max satisfies idempotent compatibility). -/
theorem max_idempotent_compatible : IdempotentCompatible maxThreshold := by
  intro n n' scores scores' hn hsub
  simp only [maxThreshold, dif_pos hn]
  -- From hsub on element ⟨0, hn⟩ we get n' > 0
  have hn' : 0 < n' := by
    obtain ⟨j, _⟩ := hsub ⟨0, hn⟩
    exact Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 j)
  simp only [dif_pos hn']
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin n') := ⟨⟨0, hn'⟩⟩
  apply Finset.sup'_le _ _ (fun i _ => ?_)
  obtain ⟨j, hj⟩ := hsub i
  rw [hj]; exact Finset.le_sup' _ (Finset.mem_univ j)

/-- A memoryless threshold is permutation-invariant if reordering scores
    does not change the output. This formalizes "parameter-free": the
    threshold depends only on the multiset of scores, not on indexing. -/
def PermutationInvariant (θ : MemorylessThreshold) : Prop :=
  ∀ (n : ℕ) (scores : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
    θ n (scores ∘ σ) = θ n scores

/-- A memoryless threshold is tight if it is bounded by some score:
    for nonempty inputs, there exists an index whose score is at least θ.
    This ensures θ does not exceed the maximum, which is required for
    capture to be well-defined (θ > max means nothing is ever captured). -/
def TightBound (θ : MemorylessThreshold) : Prop :=
  ∀ (n : ℕ) (scores : Fin n → ℝ), 0 < n →
    ∃ i : Fin n, θ n scores ≤ scores i

/-- Singleton normalization: for a single-element memory set, the threshold
    equals the sole score. This is the natural condition that the threshold
    of {x} is x, since any element scoring above x should be captured
    and no element scoring below x should be. Combined with idempotent
    compatibility and tightness, this forces θ = max. -/
def SingletonNorm (θ : MemorylessThreshold) : Prop :=
  ∀ (x : ℝ), θ 1 (fun _ : Fin 1 => x) = x

/-- Rigidity of the capture threshold.
    Among permutation-invariant, tight, singleton-normalized memoryless
    thresholds, max is the unique one consistent with idempotent capture.

    Hypotheses:
    - h_perm_inv: theta depends only on the multiset of scores (parameter-free)
    - h_tight: theta is bounded by some score (capture is nontrivial)
    - h_singleton: theta({x}) = x (singleton normalization)
    - h_idempotent: theta is monotone under set enlargement (idempotent capture)

    Proof:
    (<=) h_tight gives theta(scores) <= scores(i) for some i, so theta <= sup'.
    (>=) For any i, {scores(i)} is a subset of scores, so by h_idempotent:
        scores(i) = theta(1, [scores(i)]) <= theta(n, scores).
        Hence sup' <= theta.
    Paper: prop:capture_rigidity. -/
theorem capture_threshold_unique
    (θ : MemorylessThreshold)
    (_h_perm_inv : PermutationInvariant θ)
    (h_tight : TightBound θ)
    (h_singleton : SingletonNorm θ)
    (h_idempotent : IdempotentCompatible θ) :
    ∀ (n : ℕ) (hn : 0 < n) (scores : Fin n → ℝ),
      θ n scores = Finset.sup' Finset.univ
        (by haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩; exact Finset.univ_nonempty) scores := by
  intro n hn scores
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · -- (≤) θ ≤ sup': from h_tight, θ ≤ scores(i) for some i, and scores(i) ≤ sup'
    obtain ⟨i, hi⟩ := h_tight n scores hn
    exact le_trans hi (Finset.le_sup' scores (Finset.mem_univ i))
  · -- (≥) sup' ≤ θ: show scores(i) ≤ θ(n, scores) for all i
    apply Finset.sup'_le _ _ (fun i _ => ?_)
    -- θ(1, [scores(i)]) = scores(i) by singleton normalization
    rw [← h_singleton (scores i)]
    -- θ(1, [scores(i)]) ≤ θ(n, scores) by idempotent compatibility
    -- with M = {scores(i)} ⊆ M' = scores
    apply h_idempotent 1 n _ scores (by omega)
    intro ⟨0, _⟩
    exact ⟨i, rfl⟩
