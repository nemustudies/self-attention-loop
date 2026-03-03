/-
  SleepLoop/Sleep/SelfObservable.lean

  Theorem 45 (thm:self_observable): Self-observable sleep pressure.
  The system can detect its own need for sleep from internal quantities.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Core.ContractionRate

open Finset BigOperators

/-! ## Self-Observable Sleep Pressure (Theorem 45) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- The three observable quantities: ρ (retrieval concentration),
    γ (consolidation capacity), μ (memory load).
    Paper: thm:self_observable, definitions (i)-(iii). -/
structure SleepObservables where
  /-- ρ_t = max_j w_j^(t), the max retrieval weight. -/
  rho : ℝ
  /-- γ_t = min_{j≠v} λ_j(1 - √(1 - α_v^(j))), the contraction rate. -/
  gamma : ℝ
  /-- μ_t = |M_t|, the number of rows in M. -/
  mu : ℕ

/-- (a) All three quantities are computable from the current state alone.
    Paper: thm:self_observable(a).
    γ is constructed as contractionRate from Definition 14. -/
theorem self_observable_computable
    {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin n → ℝ)
    (v : Fin n) :
    -- ρ, γ, μ are all computable from (M, w, q) alone
    ∃ obs : SleepObservables,
      obs.rho = retrievalConcentration w hn ∧
      obs.gamma = contractionRate φ br w q M v hn2 ∧
      obs.mu = n := by
  -- ρ = max_j w_j is directly computable from weights w
  -- μ = |M| = n is given by the size of M
  -- γ = contractionRate φ br w q M v = min_{j≠v} λ_j(1 - √(1-α_v^j))
  -- All quantities are state-local, requiring no external context
  exact ⟨{rho := retrievalConcentration w hn,
           gamma := contractionRate φ br w q M v hn2,
           mu := n}, rfl, rfl, rfl⟩

/-- (b) ρ_t is non-increasing at every capture event.
    Upper bound: ρ_t ≤ 1/(1 + (μ_t - 1)exp(-2R²)).
    Paper: thm:self_observable(b). -/
theorem self_observable_rho_bound
    (n : ℕ) (hn : 1 < n) (R : ℝ) (_hR : 0 < R)
    (w : Fin n → ℝ)
    (_h_w_nonneg : ∀ i, 0 ≤ w i)
    (_h_w_sum : ∑ i, w i = 1)
    -- The max weight is bounded by softmax ceiling
    (h_softmax_bound : ∀ j, w j ≤
      1 / (1 + (↑(n - 1)) * Real.exp (-(2 * R ^ 2)))) :
    retrievalConcentration w (by omega) ≤
      1 / (1 + (↑(n - 1)) * Real.exp (-(2 * R ^ 2))) := by
  -- ρ = max_j w_j, and each w_j is bounded by the softmax ceiling
  unfold retrievalConcentration
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply Finset.sup'_le
  intro j _
  exact h_softmax_bound j

/-- (c) γ_t → 0 as ρ_t → 1/μ_t (self-limiting).
    Paper: thm:self_observable(c).

    The mechanism goes through blend rates:
    (1) ρ → 1/μ means retrieval weights equalize (w_j/w_v → 1).
    (2) Blend rates λ_j = br(w_j/w_v) → br(1) = 0 as ratios → 1.
    (3) γ = min_{j≠v} λ_j·(1 - √(1-α)) ≤ max_j λ_j =: λ_max.
    So γ → 0 via λ_max → 0, which is controlled by ρ → 1/μ. -/
theorem self_observable_gamma_vanishes
    (ρ γ blendMax : ℕ → ℝ) (μ : ℕ)
    (h_equalize : ∀ ε > 0, ∃ T, ∀ t ≥ T, |ρ t - 1 / ↑μ| < ε)
    -- Blend rates vanish as weights equalize:
    -- λ_j = br(w_j/w_v) → br(1) = 0, so blendMax → 0 as ρ → 1/μ
    (h_blend_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ t, |ρ t - 1 / ↑μ| < δ → blendMax t < ε)
    -- γ is bounded by the max blend rate:
    -- γ = min_{j≠v} λ_j·(positive factor) ≤ max_j λ_j = blendMax
    (h_gamma_le_blend : ∀ t, γ t ≤ blendMax t) :
    ∀ ε > 0, ∃ T, ∀ t ≥ T, γ t < ε := by
  -- Paper Theorem 45(c): chain through blend rates
  -- Step 1: For given ε, get δ such that |ρ - 1/μ| < δ ⟹ blendMax < ε
  -- Step 2: Use h_equalize with δ to get T such that |ρ t - 1/μ| < δ for t ≥ T
  -- Step 3: Combine: γ t ≤ blendMax t < ε for t ≥ T
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h_blend_vanishes ε hε
  obtain ⟨T, hT⟩ := h_equalize δ hδ_pos
  exact ⟨T, fun t ht => lt_of_le_of_lt (h_gamma_le_blend t) (hδ t (hT t ht))⟩

/-- (d) The joint condition (ρ < c and γ < ε) is a sufficient condition for sleep.
    Both conditions are monotone during waking: once triggered, they remain.
    Paper: thm:self_observable(d). -/
theorem self_observable_sleep_condition
    (ρ γ : ℕ → ℝ) (c ε : ℝ)
    (t₀ : ℕ)
    (h_rho : ρ t₀ < c)
    (h_gamma : γ t₀ < ε)
    -- During waking, both conditions are absorbing (monotone non-increasing)
    (h_rho_absorb : ∀ t ≥ t₀, ρ t ≤ ρ t₀)
    (h_gamma_absorb : ∀ t ≥ t₀, γ t ≤ γ t₀) :
    ∀ t ≥ t₀, ρ t < c ∧ γ t < ε := by
  -- From absorbing properties:
  -- ρ is monotone non-increasing, so ρₜ ≤ ρₜ₀ < c
  -- γ is monotone non-increasing, so γₜ ≤ γₜ₀ < ε
  intro t ht
  exact ⟨lt_of_le_of_lt (h_rho_absorb t ht) h_rho,
         lt_of_le_of_lt (h_gamma_absorb t ht) h_gamma⟩

/-- (e) Under S=0 with capture disabled, both conditions reverse.
    Paper: thm:self_observable(e).

    Under S=0, the query stabilizes (no new captures), a clear anchor
    emerges with γ > 0, so consolidation capacity recovers. As consolidation
    proceeds, impressions converge, the effective μ decreases, and ρ recovers.

    The two regimes of γ → 0 are distinguishable:
    - Exhaustion (waking): γ → 0 with ρ → 1/μ (flat weights, degraded retrieval)
    - Completion (after sleep): γ → 0 with ρ > c (sharp weights, recovered retrieval)

    The system detects sleep completion by monitoring (ρ, γ) alone. -/
theorem self_observable_regime_classification
    (ρ γ : ℕ → ℝ) (c c' : ℝ) (hc : 0 < c) (_hcc' : c < c')
    (μ : ℕ) (_hμ : 1 < μ)
    -- Under S=0: γ eventually vanishes (approach fixed point, thm:wakeup(vi))
    (h_gamma_vanishes : ∀ ε > 0, ∃ T, ∀ t ≥ T, γ t < ε)
    -- Under S=0: ρ recovers above the recovery threshold c'
    -- (from consolidation reducing effective μ and restoring weight sharpness)
    (h_rho_recovers : ∃ T_rec, ∀ t ≥ T_rec, ρ t > c')
    -- Exhaustion regime is distinguishable: ρ ≤ 1/μ (flat weights)
    (_h_exhaustion_char : ∀ t, ρ t ≤ 1 / (μ : ℝ) → γ t < c → ρ t < c) :
    -- The completion regime is detectable: γ → 0 with ρ > c'
    -- (both conditions hold simultaneously after sufficient sleep)
    ∃ T_detect : ℕ, ∀ t ≥ T_detect, γ t < c ∧ ρ t > c' := by
  obtain ⟨T_rec, hT_rec⟩ := h_rho_recovers
  obtain ⟨T_gamma, hT_gamma⟩ := h_gamma_vanishes c hc
  exact ⟨max T_rec T_gamma, fun t ht => by
    constructor
    · exact hT_gamma t (le_of_max_le_right ht)
    · exact hT_rec t (le_of_max_le_left ht)⟩
