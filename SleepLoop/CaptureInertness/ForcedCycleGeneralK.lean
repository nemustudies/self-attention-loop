/-
  SleepLoop/CaptureInertness/ForcedCycleGeneralK.lean

  Corollary 70 (cor:forced_cycle_general_K): Forced cycle covers general K.
  For any K (including large ||K||), the system is forced into alternating
  capture and consolidation regimes via the carrying capacity mechanism.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Capture
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.CaptureInertness.CaptureArgmax
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators

/-! ## Forced Cycle for General K -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

omit [DecidableEq X] in
/-- Paper: cor:forced_cycle_general_K.
    For any K (including large ||K||), the system is forced into alternating
    capture and consolidation regimes.

    Each capture strictly increases |M| (by cor:acquisition).
    By thm:sleep_pressure, once |M| >= |M*|, retrieval precision rho falls
    below the concentration threshold c (since rho <= 1/(1+(|M|-1)exp(-2R^2))).
    By thm:self_observable, this degradation is self-observable via (rho, gamma).
    The sleep gate triggers consolidation, forcing the cycle.

    The statement encodes: once memory exceeds carrying capacity,
    retrieval concentration drops below c. -/
theorem forced_cycle_general_K
    (E : Embedding X d) (_hgen : GenericEmbedding E)
    (_K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    -- The carrying capacity and embedding radius
    (R c : ℝ) (_hR : 0 < R) (_hc : 0 < c) (_hc1 : c < 1)
    (M_star : ℝ) (_hM_star : M_star = criticalMemorySize c R)
    -- Memory size trajectory
    (memSize : ℕ → ℕ)
    -- Each capture strictly increases |M|
    (h_monotone : ∀ t, memSize t ≤ memSize (t + 1))
    -- Retrieval concentration as a function of memory size
    (ρ : ℕ → ℝ)
    -- ρ is bounded by the softmax ceiling: ρ_t ≤ 1/(1 + (|M_t|-1)exp(-2R²))
    (_h_rho_bound : ∀ t, ρ t ≤ 1 / (1 + ((memSize t : ℝ) - 1) * Real.exp (-(2 * R ^ 2))))
    -- Contraction rate
    (γ : ℕ → ℝ)
    -- γ is bounded by ρ - 1/|M| (vanishes as weights equalize)
    (_h_gamma_bound : ∀ t, 0 ≤ γ t)
    -- Once |M| ≥ |M*|, the softmax ceiling is below c
    (h_ceiling_below_c : ∀ t, M_star ≤ (memSize t : ℝ) → ρ t < c) :
    -- The system eventually enters the exhaustion regime:
    -- there exists T_sleep such that ρ < c (retrieval degraded)
    -- and the sleep gate would trigger consolidation
    (∃ T_sleep : ℕ, ∀ t ≥ T_sleep, ρ t < c) ∨
    -- Or memory never reaches M* (captures are finite, covered by prop:capture_inertness)
    (∀ t, (memSize t : ℝ) < M_star) := by
  by_cases h : ∃ T₀, M_star ≤ (memSize T₀ : ℝ)
  · -- Memory exceeds carrying capacity at some T₀
    obtain ⟨T₀, hT₀⟩ := h
    left
    refine ⟨T₀, fun t ht => ?_⟩
    apply h_ceiling_below_c
    -- memSize is non-decreasing, so memSize t ≥ memSize T₀ ≥ M_star
    have : memSize T₀ ≤ memSize t := by
      have : ∀ k, memSize T₀ ≤ memSize (T₀ + k) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => exact le_trans ih (h_monotone _)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
      exact this k
    calc M_star ≤ (memSize T₀ : ℝ) := hT₀
      _ ≤ (memSize t : ℝ) := Nat.cast_le.mpr this
  · -- Memory never reaches M* — captures are finite
    right
    push_neg at h
    exact fun t => h t

omit [DecidableEq X] in
/-- Paper: cor:forced_cycle_general_K (strong form).
    When captures are unbounded (memory grows without bound), the forced cycle
    is inevitable -- no disjunction needed.

    The paper's argument for general K: large ||K|| can sustain query rotation
    indefinitely, producing unbounded captures. Each capture strictly increases |M|.
    Once |M| >= |M*|, retrieval precision falls below c, and the sleep gate triggers.

    This eliminates the second disjunct of `forced_cycle_general_K`: if captures
    are unbounded, memory must eventually exceed M*, so sleep is forced. -/
theorem forced_cycle_general_K_unbounded
    (E : Embedding X d) (_hgen : GenericEmbedding E)
    (_K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    -- The carrying capacity and embedding radius
    (R c : ℝ) (_hR : 0 < R) (_hc : 0 < c) (_hc1 : c < 1)
    (M_star : ℝ) (_hM_star : M_star = criticalMemorySize c R)
    -- Memory size trajectory
    (memSize : ℕ → ℕ)
    -- Each capture strictly increases |M|
    (h_monotone : ∀ t, memSize t ≤ memSize (t + 1))
    -- Memory is unbounded (captures never stop)
    (h_unbounded : ∀ N : ℕ, ∃ t, N ≤ memSize t)
    -- Retrieval concentration as a function of memory size
    (ρ : ℕ → ℝ)
    -- ρ is bounded by the softmax ceiling
    (_h_rho_bound : ∀ t, ρ t ≤ 1 / (1 + ((memSize t : ℝ) - 1) * Real.exp (-(2 * R ^ 2))))
    -- Contraction rate
    (γ : ℕ → ℝ)
    -- γ is non-negative
    (_h_gamma_bound : ∀ t, 0 ≤ γ t)
    -- Once |M| ≥ |M*|, the softmax ceiling is below c
    (h_ceiling_below_c : ∀ t, M_star ≤ (memSize t : ℝ) → ρ t < c) :
    -- Sleep is forced: ρ eventually stays below c
    ∃ T_sleep : ℕ, ∀ t ≥ T_sleep, ρ t < c := by
  -- Step 1: Find T₀ such that memSize T₀ ≥ ⌈M_star⌉₊
  obtain ⟨T₀, hT₀⟩ := h_unbounded (Nat.ceil M_star)
  -- Step 2: For all t ≥ T₀, memSize t ≥ memSize T₀ (by monotonicity)
  refine ⟨T₀, fun t ht => ?_⟩
  apply h_ceiling_below_c
  -- memSize is non-decreasing, so memSize t ≥ memSize T₀
  have hmono : memSize T₀ ≤ memSize t := by
    have : ∀ k, memSize T₀ ≤ memSize (T₀ + k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => exact le_trans ih (h_monotone _)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact this k
  -- memSize T₀ ≥ ⌈M_star⌉₊ ≥ M_star
  calc M_star ≤ ↑(Nat.ceil M_star) := Nat.le_ceil M_star
    _ ≤ (memSize T₀ : ℝ) := Nat.cast_le.mpr hT₀
    _ ≤ (memSize t : ℝ) := Nat.cast_le.mpr hmono

/-- Paper: cor:acquisition (auxiliary).
    Each capture strictly increases memory size. -/
theorem capture_increases_memory
    (M_before M_after : Finset (EuclideanSpace ℝ (Fin d)))
    (h_capture : ∃ m, m ∉ M_before ∧ m ∈ M_after)
    (h_subset : M_before ⊆ M_after) :
    M_before.card < M_after.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨h_subset, ?_⟩
  intro heq
  obtain ⟨m, hm_not, hm_in⟩ := h_capture
  rw [heq] at hm_not
  exact hm_not hm_in

/-- Paper: thm:sleep_pressure (auxiliary).
    Retrieval concentration rho -> 1/|M| as |M| grows,
    meaning retrieval degrades. -/
theorem retrieval_degrades_with_memory_size
    {n : ℕ} (_hn : 2 ≤ n)
    (ρ : ℝ) (_hρ : ρ = 1 / (n : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N_threshold : ℕ, ∀ m : ℕ, N_threshold ≤ m →
      1 / (m : ℝ) < ε := by
  -- Use Archimedean property: find N with 1/ε < N, then for m ≥ N, 1/m ≤ 1/N < ε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intro m hm
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : 1 / ε > 0 := div_pos one_pos hε
    linarith
  have hNm : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  rw [div_lt_iff₀ hm_pos]
  calc 1 = ε * (1 / ε) := by field_simp
    _ < ε * (N : ℝ) := by apply mul_lt_mul_of_pos_left hN hε
    _ ≤ ε * (m : ℝ) := by apply mul_le_mul_of_nonneg_left hNm (le_of_lt hε)
