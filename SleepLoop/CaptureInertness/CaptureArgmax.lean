/-
  SleepLoop/CaptureInertness/CaptureArgmax.lean

  Theorem 67 (thm:capture_argmax): Capture-argmax bound.
  Under constant S with generic embedding E, the total number of
  captures is bounded by the total E-argmax transitions of q plus 1.
  Within any period where τ* = argmax_τ q·E(τ) is constant,
  capture fires at most once.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Capture
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.ConvexHullInvariance
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators

/-! ## Capture-Argmax Bound -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- Generic embedding: for any q in conv(E(X)), the argmax of q . E(tau) is unique.
    Paper: thm:capture_argmax (hypothesis). -/
def GenericEmbedding (E : Embedding X d) : Prop :=
  ∀ q : EuclideanSpace ℝ (Fin d),
    ∃! τ : X, ∀ τ' : X, edot q (E.map τ') ≤ edot q (E.map τ)

/-- The E-argmax: τ* = argmax_τ q·E(τ).
    Returns the element achieving the maximum inner product with q. -/
noncomputable def eArgmax (E : Embedding X d) (q : EuclideanSpace ℝ (Fin d))
    [Nonempty X] : X :=
  Classical.choose (Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun τ => edot q (E.map τ)))

omit [DecidableEq X] in
/-- Helper: eArgmax E q achieves the sup of scores. -/
lemma eArgmax_spec [Nonempty X] (E : Embedding X d) (q : EuclideanSpace ℝ (Fin d)) :
    edot q (E.map (eArgmax E q)) =
      Finset.sup' Finset.univ Finset.univ_nonempty (fun τ => edot q (E.map τ)) := by
  have h := Classical.choose_spec
    (Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun τ : X => edot q (E.map τ)))
  exact h.2.symm

omit [DecidableEq X] in
/-- Helper: eArgmax E q is a maximizer of q·E(τ). -/
lemma eArgmax_is_max [Nonempty X] (E : Embedding X d) (q : EuclideanSpace ℝ (Fin d))
    (τ : X) : edot q (E.map τ) ≤ edot q (E.map (eArgmax E q)) := by
  rw [eArgmax_spec]
  exact Finset.le_sup' (fun τ => edot q (E.map τ)) (Finset.mem_univ τ)

omit [DecidableEq X] in
/-- Helper: If τ is the unique argmax (by GenericEmbedding), then eArgmax E q = τ. -/
lemma eArgmax_eq_unique [Nonempty X] (E : Embedding X d) (q : EuclideanSpace ℝ (Fin d))
    (τ : X) (_hτ : ∀ τ' : X, edot q (E.map τ') ≤ edot q (E.map τ))
    (huniq : ∀ τ' : X, (∀ τ'' : X, edot q (E.map τ'') ≤ edot q (E.map τ')) → τ' = τ) :
    eArgmax E q = τ := by
  apply huniq
  exact eArgmax_is_max E q

/-- An E-argmax transition occurs when the argmax changes between steps. -/
noncomputable def eArgmaxTransitions [Nonempty X]
    (E : Embedding X d) (q : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℕ :=
  Finset.card ((Finset.range T).filter fun t =>
    eArgmax E (q t) ≠ eArgmax E (q (t + 1)))

omit [DecidableEq X] in
/-- Paper: thm:capture_argmax (inert period).
    Under constant S with generic E, within any period where
    tau* = argmax_tau q . E(tau) is constant, capture fires at most once.

    Key idea: Once E(tau*) is captured, it achieves the highest score
    among all m_k in conv(E(X)), so the capture condition
    q . E(tau) > max_k q . m_k fails for all tau. -/
theorem capture_argmax_inert_period
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (E : Embedding X d) (_hgen : GenericEmbedding E)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    -- All memories lie in conv(E(X))
    (_h_hull : ∀ k, ∃ α : X → ℝ,
      (∀ τ, 0 ≤ α τ) ∧ ∑ τ, α τ = 1 ∧ M k = ∑ τ, α τ • E.map τ)
    -- τ* is the E-argmax
    (τ_star : X)
    (hτ : ∀ τ : X, edot q (E.map τ) ≤ edot q (E.map τ_star))
    -- E(τ*) is already in M (as the k-th row)
    (k_star : Fin n)
    (hk : M k_star = E.map τ_star) :
    -- Then the capture threshold ≥ max_τ q·E(τ), so capture is inert
    ∀ τ : X, edot q (E.map τ) ≤ edot q (M k_star) := by
  intro τ
  rw [hk]
  exact hτ τ

/-- Paper: thm:capture_argmax (counting version).
    Total captures <= total E-argmax transitions + 1.

    The paper proves this by partitioning [0,T] into maximal intervals where the
    E-argmax is constant. Within each such interval, capture fires at most once
    (by capture_argmax_inert_period above: once E(tau*) is in M, it dominates
    all convex combinations). The counting version requires this combinatorial
    hypothesis, which we encode as `h_inert`: within any interval where the
    E-argmax is constant, C contains at most one element. -/
theorem capture_argmax_bound [Nonempty X]
    (E : Embedding X d) (_hgen : GenericEmbedding E)
    -- The trajectory of queries and memory states
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    (T : ℕ)
    -- Capture times: when new impressions were added
    (C : Finset ℕ)
    (hC : C ⊆ Finset.range (T + 1))
    -- Paper's key property (from capture_argmax_inert_period):
    -- Within any constant-argmax interval, at most one capture occurs.
    -- Formally: if t₁ < t₂ are both in C, then the E-argmax must change
    -- at some step between them (there is a transition in (t₁, t₂]).
    (h_inert : ∀ t₁ t₂ : ℕ, t₁ ∈ C → t₂ ∈ C → t₁ < t₂ →
      ∃ s, t₁ ≤ s ∧ s < t₂ ∧ eArgmax E (q s) ≠ eArgmax E (q (s + 1))) :
    -- Number of captures ≤ number of argmax transitions + 1
    C.card ≤ eArgmaxTransitions E q T + 1 := by
  unfold eArgmaxTransitions
  -- Strategy: construct an injection from C' = C \ {max(C)} into the transition set.
  -- For each t ∈ C', let succ(t) = min of {u ∈ C | u > t}, and choose a transition
  -- witness s(t) with t ≤ s(t) < succ(t) from h_inert.
  -- The witnesses are distinct because the intervals [t, succ(t)) are disjoint.
  -- Then |C'| ≤ |transitions|, so |C| ≤ |transitions| + 1.
  set Trans := (Finset.range T).filter
    fun t => eArgmax E (q t) ≠ eArgmax E (q (t + 1)) with hTrans_def
  by_cases hC_empty : C = ∅
  · simp [hC_empty]
  have hC_ne : C.Nonempty := Finset.nonempty_of_ne_empty hC_empty
  -- Define C' = C minus its maximum
  set tmax := C.max' hC_ne with htmax_def
  set C' := C.erase tmax with hC'_def
  have htmax_mem : tmax ∈ C := Finset.max'_mem C hC_ne
  have hC'_card : C'.card = C.card - 1 := Finset.card_erase_of_mem htmax_mem
  -- It suffices to show C'.card ≤ Trans.card (then C.card = C'.card + 1 ≤ Trans.card + 1)
  suffices h_inj_bound : C'.card ≤ Trans.card by omega
  -- For each t ∈ C', the set {u ∈ C | u > t} is nonempty (tmax is in it)
  have h_succ_ne : ∀ t ∈ C', (C.filter (· > t)).Nonempty := by
    intro t ht
    refine ⟨tmax, Finset.mem_filter.mpr ⟨htmax_mem, ?_⟩⟩
    have : t ≠ tmax := Finset.ne_of_mem_erase ht
    have : t ≤ tmax := Finset.le_max' C t (Finset.mem_of_mem_erase ht)
    omega
  -- Define the successor function
  let succC : ∀ t, t ∈ C' → ℕ := fun t ht => (C.filter (· > t)).min' (h_succ_ne t ht)
  -- Properties of succC
  have h_succ_mem : ∀ t (ht : t ∈ C'), succC t ht ∈ C := by
    intro t ht
    exact Finset.mem_of_mem_filter _ (Finset.min'_mem _ _)
  have h_succ_gt : ∀ t (ht : t ∈ C'), t < succC t ht := by
    intro t ht
    have := (Finset.mem_filter.mp (Finset.min'_mem _ (h_succ_ne t ht))).2
    exact this
  have h_succ_le : ∀ t (ht : t ∈ C') (u : ℕ), u ∈ C → t < u → succC t ht ≤ u := by
    intro t ht u hu htu
    exact Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, htu⟩)
  -- For each t ∈ C', h_inert gives a transition witness between t and succC t
  have h_witness : ∀ t (ht : t ∈ C'), ∃ s, t ≤ s ∧ s < succC t ht ∧
      eArgmax E (q s) ≠ eArgmax E (q (s + 1)) := by
    intro t ht
    exact h_inert t (succC t ht) (Finset.mem_of_mem_erase ht)
      (h_succ_mem t ht) (h_succ_gt t ht)
  -- Choose the witness function
  -- We need to build f : C' → Trans and show it's injective.
  -- Use Finset.card_le_card_of_injOn or Finset.card_le_card with image.
  -- Define f(t) = Classical.choose (h_witness t ht)
  -- We need f to map into Trans and be injective on C'.
  -- Properties of chosen witnesses
  have h_wit_spec : ∀ t (ht : t ∈ C'),
      let s := Classical.choose (h_witness t ht)
      t ≤ s ∧ s < succC t ht ∧ eArgmax E (q s) ≠ eArgmax E (q (s + 1)) :=
    fun t ht => Classical.choose_spec (h_witness t ht)
  -- Define f as a function on ℕ (defaulting to 0 outside C')
  let f : ℕ → ℕ := fun t =>
    if ht : t ∈ C' then Classical.choose (h_witness t ht) else 0
  -- f maps C' into Trans
  have hf_mem : ∀ t ∈ C', f t ∈ Trans := by
    intro t ht
    simp only [f, dif_pos ht]
    have spec := h_wit_spec t ht
    rw [hTrans_def]
    refine Finset.mem_filter.mpr ⟨?_, spec.2.2⟩
    rw [Finset.mem_range]
    have h_succ_bound : succC t ht ≤ T := by
      have : succC t ht ∈ C := h_succ_mem t ht
      have : succC t ht ∈ Finset.range (T + 1) := hC this
      rw [Finset.mem_range] at this
      omega
    omega
  -- f is injective on C': if t₁ < t₂ in C', then f(t₁) < f(t₂)
  -- because f(t₁) < succC(t₁) ≤ t₂ ≤ f(t₂)
  have hf_injOn : Set.InjOn f ↑C' := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe] at ht₁ ht₂
    simp only [f, dif_pos ht₁, dif_pos ht₂] at heq
    by_contra hne
    -- WLOG t₁ < t₂ (or t₂ < t₁)
    rcases Nat.lt_or_gt_of_ne hne with h_lt | h_lt
    · -- t₁ < t₂
      have spec₁ := h_wit_spec t₁ ht₁
      have spec₂ := h_wit_spec t₂ ht₂
      -- f(t₁) < succC(t₁) ≤ t₂ ≤ f(t₂)
      have h1 : Classical.choose (h_witness t₁ ht₁) < succC t₁ ht₁ := spec₁.2.1
      have h2 : succC t₁ ht₁ ≤ t₂ :=
        h_succ_le t₁ ht₁ t₂ (Finset.mem_of_mem_erase ht₂) h_lt
      have h3 : t₂ ≤ Classical.choose (h_witness t₂ ht₂) := spec₂.1
      omega
    · -- t₂ < t₁: symmetric
      have spec₁ := h_wit_spec t₁ ht₁
      have spec₂ := h_wit_spec t₂ ht₂
      have h1 : Classical.choose (h_witness t₂ ht₂) < succC t₂ ht₂ := spec₂.2.1
      have h2 : succC t₂ ht₂ ≤ t₁ :=
        h_succ_le t₂ ht₂ t₁ (Finset.mem_of_mem_erase ht₁) h_lt
      have h3 : t₁ ≤ Classical.choose (h_witness t₁ ht₁) := spec₁.1
      omega
  -- Now: |C'| = |f(C')| ≤ |Trans|
  have h_image_card : (C'.image f).card = C'.card :=
    Finset.card_image_of_injOn hf_injOn
  have h_image_sub : C'.image f ⊆ Trans := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hf_mem t ht
  calc C'.card
      = (C'.image f).card := h_image_card.symm
    _ ≤ Trans.card := Finset.card_le_card h_image_sub
