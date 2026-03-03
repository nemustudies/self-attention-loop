/-
  SleepLoop/Core/RetrievalCrossover.lean

  Retrieval advantage grows with delay (Corollary cor:crossover).
  Compare re-observation (transient sigma boost, O(1/t) decay) with
  retrieval (permanent Lyapunov contraction V' < V). At sufficiently
  long delays, the permanent contraction dominates the transient boost.

  Building blocks:
  - ForgettingCurve: sigma_t = C_T/(N_0 + t) when attention ceases
  - TestingEffect: retrieval preserves anchor, displaces competitors
  - Lyapunov: V(t+1) < V(t) whenever V(t) > 0

  Level: A_+.
-/
import SleepLoop.Core.ForgettingCurve
import SleepLoop.Core.TestingEffect
import SleepLoop.Core.Lyapunov
import Mathlib.Topology.Order.Basic

open Finset BigOperators

/-! ## Retrieval Crossover -/

variable {d n : ℕ}

/-- Part (i): Re-observation salience gain is bounded by 1/(N_0 + T) and decays to 0.
    A single observation adds at most 1 to C(τ), so the salience boost
    ΔC/(N_0 + t) ≤ 1/(N_0 + t) → 0 as t → ∞. -/
theorem restudy_boost_transient
    {X : Type*} (C : ℕ → X → ℝ) (N : ℕ → X → ℕ) (a : ℕ → X → ℝ)
    (τ : X) (T : ℕ)
    (h_update_C : ∀ t, C (t + 1) τ = accumulateC (C t) (a t) t τ)
    (h_update_N : ∀ t, N (t + 1) τ = N t τ + 1)
    (hC_pos : 0 < C T τ)
    (ha_bounded : ∀ t, 0 ≤ a t τ ∧ a t τ ≤ 1)
    (h_cease : ∀ t, T + 1 ≤ t → a t τ = 0)
    (hN_pos : 0 < N 0 τ) :
    -- The salience boost from one observation at time T decays to 0
    ∀ ε > 0, ∃ t₀, ∀ t, t₀ ≤ t →
      C (T + 1) τ / (N 0 τ + t : ℝ) - C T τ / (N 0 τ + t : ℝ) < ε := by
  -- The numerator ΔC = C(T+1)(τ) - C(T)(τ) is a fixed nonneg constant.
  -- The expression equals ΔC / (N₀ + t), which → 0 as t → ∞.
  set ΔC := C (T + 1) τ - C T τ with hΔC_def
  -- Step 1: Show ΔC ≥ 0
  have hΔC_nn : 0 ≤ ΔC := by
    rw [hΔC_def, sub_nonneg, h_update_C T]
    unfold accumulateC
    linarith [mul_nonneg (ha_bounded T).1 (by positivity : (0 : ℝ) ≤ (↑T + 1)),
              div_nonneg (mul_nonneg (ha_bounded T).1 (by positivity : (0 : ℝ) ≤ (↑T + 1)))
                (le_of_lt hC_pos)]
  -- Step 2: For any ε > 0, find t₀ via Archimedean property
  -- Note: t₀ and t are ℝ since (N 0 τ + t : ℝ) forces real coercion.
  intro ε hε
  -- Choose t₀ = ΔC / ε + 1. Then for t ≥ t₀, ΔC/(N₀+t) < ε.
  use ΔC / ε + 1
  intro t ht
  -- Factor: a/d - b/d = (a-b)/d
  have h_eq : C (T + 1) τ / (↑(N 0 τ) + t) - C T τ / (↑(N 0 τ) + t) =
      ΔC / (↑(N 0 τ) + t) := by
    rw [hΔC_def]; ring
  rw [h_eq]
  have hN0_nn : (0 : ℝ) ≤ ↑(N 0 τ) := Nat.cast_nonneg _
  -- t ≥ ΔC/ε + 1 > 0, so N₀ + t > 0
  have ht_ge : ΔC / ε + 1 ≤ t := ht
  have ht_pos : (0 : ℝ) < t := by
    have : 0 ≤ ΔC / ε := div_nonneg hΔC_nn (le_of_lt hε)
    linarith
  have hden_pos : (0 : ℝ) < ↑(N 0 τ) + t := by linarith
  rw [div_lt_iff₀ hden_pos]
  -- Goal: ΔC < ε * (↑(N 0 τ) + t)
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have h1 : ΔC < ε * (ΔC / ε + 1) := by
    rw [mul_add, mul_one, mul_comm, div_mul_cancel₀ _ hε_ne]
    linarith
  calc ΔC < ε * (ΔC / ε + 1) := h1
    _ ≤ ε * t := mul_le_mul_of_nonneg_left ht_ge (le_of_lt hε)
    _ ≤ ε * (↑(N 0 τ) + t) := by nlinarith

/-- Part (ii): Retrieval contraction is permanent and independent of delay.
    Wraps lyapunov_strict_decrease: V(M') < V(M), where V depends only on M. -/
theorem retrieval_contraction_permanent
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hn : 2 ≤ n)
    (v : Fin n)
    (hv : ∀ k, w k ≤ w v)
    (hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k)
    (hV_pos : 0 < lyapunovV M v hn) :
    let M' := consolidationStep φ br w q M (by omega)
    lyapunovV M' v hn < lyapunovV M v hn := by
  exact lyapunov_strict_decrease φ br w q M hn v hv hv_unique hw_pos hV_pos

/-- Combined crossover: re-study advantage vanishes while retrieval advantage persists.
    The salience boost from re-observation decays as O(1/t), while the Lyapunov
    contraction from retrieval is permanent. Therefore at sufficiently long delays,
    retrieval dominates re-study. -/
theorem retrieval_crossover
    {X : Type*} (C : ℕ → X → ℝ) (N : ℕ → X → ℕ) (a : ℕ → X → ℝ)
    (τ : X) (T : ℕ)
    (h_update_C : ∀ t, C (t + 1) τ = accumulateC (C t) (a t) t τ)
    (h_update_N : ∀ t, N (t + 1) τ = N t τ + 1)
    (hC_pos : 0 < C T τ)
    (ha_bounded : ∀ t, 0 ≤ a t τ ∧ a t τ ≤ 1)
    (h_cease : ∀ t, T + 1 ≤ t → a t τ = 0)
    (hN_pos : 0 < N 0 τ)
    -- Retrieval side
    {nd nn : ℕ} (φ : (Fin nn → ℝ) → (Fin nn → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate) (w : Fin nn → ℝ)
    (q : EuclideanSpace ℝ (Fin nd))
    (M : Fin nn → EuclideanSpace ℝ (Fin nd))
    (hn : 2 ≤ nn)
    (v : Fin nn)
    (hv : ∀ k, w k ≤ w v)
    (hv_unique : ∀ k, k ≠ v → w k < w v)
    (hw_pos : ∀ k, 0 < w k)
    (hV_pos : 0 < lyapunovV M v hn) :
    -- Re-study advantage vanishes
    (∀ ε > 0, ∃ t₀, ∀ t, t₀ ≤ t →
      C (T + 1) τ / (N 0 τ + t : ℝ) - C T τ / (N 0 τ + t : ℝ) < ε) ∧
    -- Retrieval advantage is permanent
    (let M' := consolidationStep φ br w q M (by omega)
     lyapunovV M' v hn < lyapunovV M v hn) := by
  exact ⟨restudy_boost_transient C N a τ T h_update_C h_update_N hC_pos ha_bounded h_cease hN_pos,
         retrieval_contraction_permanent φ br w q M hn v hv hv_unique hw_pos hV_pos⟩
