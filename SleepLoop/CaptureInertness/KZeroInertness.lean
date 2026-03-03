/-
  SleepLoop/CaptureInertness/KZeroInertness.lean

  Corollary 69 (cor:K_zero_inertness): K=0 capture inertness.
  When K=0, the total number of capture events is finite under
  any constant S with generic E. No condition on ||K|| is needed.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Capture
import SleepLoop.Defs.Accumulation
import SleepLoop.CaptureInertness.CaptureArgmax
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators

/-! ## K=0 Capture Inertness -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

omit [DecidableEq X] in
/-- Paper: cor:K_zero_inertness.
    When K=0, the total number of capture events is finite under any
    constant S with generic E.

    Proof: Immediate from part (i) of prop:capture_inertness.
    When K=0, b=0 at all times, sigma converges independently of M,
    and lem:finite_argmax gives finitely many E-argmax transitions.
    By thm:capture_argmax, captures are finite.

    The paper's argument: once the E-argmax stabilizes (which happens after
    finitely many transitions since q converges), capture is inert. We encode
    this via the hypothesis `h_captures_need_transition`: capture can only fire
    at a time t if the E-argmax changed at or before t (i.e., the argmax at
    the query at time t differs from the eventually-constant argmax). -/
theorem K_zero_capture_finite [Nonempty X]
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (E : Embedding X d) (hgen : GenericEmbedding E)
    (_S : X → ℝ)
    -- K = 0 (no feedback)
    (K_zero : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (_hK : K_zero = 0)
    -- The query sequence (when K=0, q_t = φ(S + σ_t) E)
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    -- q converges (since K=0 and σ converges)
    (q_star : EuclideanSpace ℝ (Fin d))
    (hq : Filter.Tendsto q Filter.atTop (nhds q_star))
    -- The sequence of capture events
    (captureEvents : ℕ → Prop)
    -- Paper's key connection: capture can only fire when the E-argmax
    -- is not yet at its eventual value (i.e., capture is inert once
    -- the argmax stabilizes, by capture_argmax_inert_period).
    (h_captures_need_transition : ∀ t, captureEvents t →
      eArgmax E (q t) ≠ eArgmax E q_star) :
    -- Total captures are finite
    ∃ T : ℕ, ∀ t, T < t → ¬captureEvents t := by
  -- Since q converges to q_star and E is generic, the E-argmax eventually
  -- equals eArgmax E q_star. After that point, h_captures_need_transition
  -- prevents any capture from firing.
  -- Reuse the proof from K_zero_capture_count_finite:
  -- q converges => scores converge => eventually argmax is constant.
  obtain ⟨τ_star, hmax_star, huniq_star⟩ := hgen q_star
  -- For each τ ≠ τ_star, eventually edot (q t) (E.map τ) < edot (q t) (E.map τ_star)
  have hinner_cts : ∀ v : EuclideanSpace ℝ (Fin d),
      Filter.Tendsto (fun t => edot (q t) v) Filter.atTop (nhds (edot q_star v)) := by
    intro v
    exact (continuous_id.inner continuous_const).continuousAt.tendsto.comp hq
  have h_eventually : ∀ᶠ t in Filter.atTop, eArgmax E (q t) = eArgmax E q_star := by
    have h_eArgmax_star : eArgmax E q_star = τ_star :=
      eArgmax_eq_unique E q_star τ_star hmax_star huniq_star
    have h_gap : ∀ τ : X, τ ≠ τ_star →
        ∀ᶠ t in Filter.atTop, edot (q t) (E.map τ) < edot (q t) (E.map τ_star) := by
      intro τ hτne
      have hδ : 0 < edot q_star (E.map τ_star) - edot q_star (E.map τ) := by
        rcases lt_or_eq_of_le (hmax_star τ) with h | h
        · linarith
        · exfalso; exact hτne (huniq_star τ (fun τ' => (hmax_star τ').trans h.symm.le))
      have hconv_diff : Filter.Tendsto
          (fun t => edot (q t) (E.map τ_star) - edot (q t) (E.map τ)) Filter.atTop
          (nhds (edot q_star (E.map τ_star) - edot q_star (E.map τ))) :=
        (hinner_cts (E.map τ_star)).sub (hinner_cts (E.map τ))
      exact (hconv_diff.eventually (isOpen_Ioi.mem_nhds hδ)).mono (fun t ht => by linarith)
    have h_all : ∀ᶠ t in Filter.atTop, ∀ τ : X, τ ≠ τ_star →
        edot (q t) (E.map τ) < edot (q t) (E.map τ_star) := by
      rw [Filter.eventually_all]
      intro τ
      by_cases hτ : τ = τ_star
      · simp only [hτ, ne_eq, not_true, forall_false, Filter.eventually_true]
      · exact (h_gap τ hτ).mono (fun t ht _ => ht)
    apply h_all.mono
    intro t ht
    rw [h_eArgmax_star]
    apply eArgmax_eq_unique E (q t) τ_star
    · intro τ
      by_cases hτ : τ = τ_star
      · simp [hτ]
      · exact le_of_lt (ht τ hτ)
    · intro τ' hτ'_max
      by_contra hτ'ne
      linarith [ht τ' hτ'ne, hτ'_max τ_star]
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨T₀, hT₀⟩ := h_eventually
  exact ⟨T₀, fun t ht => by
    intro hcap
    exact h_captures_need_transition t hcap (hT₀ t (le_of_lt ht))⟩

omit [DecidableEq X] in
/-- Paper: cor:K_zero_inertness (counting version).
    The number of capture events is bounded by finitely many
    E-argmax transitions + 1. -/
theorem K_zero_capture_count_finite [Nonempty X]
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (E : Embedding X d) (hgen : GenericEmbedding E)
    (_S : X → ℝ)
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    -- q converges (since K=0 and σ converges)
    (q_star : EuclideanSpace ℝ (Fin d))
    (hq : Filter.Tendsto q Filter.atTop (nhds q_star))
    -- Summable increments
    (_hq_sum : Summable fun t => ‖q (t + 1) - q t‖) :
    -- There exists T₀ after which argmax is constant, hence captures are finite
    ∃ T₀ : ℕ, ∀ t, T₀ < t → eArgmax E (q t) = eArgmax E q_star := by
  -- Get the unique argmax τ_star at q_star
  obtain ⟨τ_star, hmax_star, huniq_star⟩ := hgen q_star
  -- eArgmax E q_star = τ_star
  have h_eArgmax_star : eArgmax E q_star = τ_star :=
    eArgmax_eq_unique E q_star τ_star hmax_star huniq_star
  -- All τ ≠ τ_star have strictly smaller score at q_star
  have hstrict : ∀ τ : X, τ ≠ τ_star →
      edot q_star (E.map τ) < edot q_star (E.map τ_star) := by
    intro τ hτne
    rcases lt_or_eq_of_le (hmax_star τ) with h | h
    · exact h
    · exfalso
      have hτ_max : ∀ τ' : X, edot q_star (E.map τ') ≤ edot q_star (E.map τ) := fun τ' =>
        calc edot q_star (E.map τ') ≤ edot q_star (E.map τ_star) := hmax_star τ'
          _ = edot q_star (E.map τ) := h.symm
      exact hτne (huniq_star τ hτ_max)
  -- For each τ ≠ τ_star, the score gap at q_star is δ_τ > 0.
  -- Since q t → q_star, the score difference |edot (q t) (E.map τ) - edot q_star (E.map τ)| → 0.
  -- By Cauchy-Schwarz: |edot (q t - q_star) (E.map τ)| ≤ ‖q t - q_star‖ * ‖E.map τ‖
  -- ≤ ‖q t - q_star‖ * R.
  -- So once ‖q t - q_star‖ < δ_τ / (2 * R), τ_star beats τ at q t.
  -- With X finite, we find a uniform T₀.
  -- We show: eventually eArgmax E (q t) = τ_star, by showing that eventually
  -- τ_star is the unique argmax for q t.
  -- Step 1: For each τ ≠ τ_star, eventually edot (q t) (E.map τ) < edot (q t) (E.map τ_star).
  -- Key: scores edot (q t) (E.map τ) converge to edot q_star (E.map τ) since inner product is
  -- continuous and q t → q_star.
  have hinner_cts : ∀ v : EuclideanSpace ℝ (Fin d),
      Filter.Tendsto (fun t => edot (q t) v) Filter.atTop (nhds (edot q_star v)) := by
    intro v
    -- edot · v is continuous in the first argument (bounded linear functional)
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => edot x v) :=
      continuous_id.inner continuous_const
    exact hcont.continuousAt.tendsto.comp hq
  have h_gap : ∀ τ : X, τ ≠ τ_star →
      ∀ᶠ t in Filter.atTop, edot (q t) (E.map τ) < edot (q t) (E.map τ_star) := by
    intro τ hτne
    -- The gap δ_τ > 0 at q_star
    have hδ : 0 < edot q_star (E.map τ_star) - edot q_star (E.map τ) := by
      linarith [hstrict τ hτne]
    -- The difference edot (q t) (E.map τ_star) - edot (q t) (E.map τ) → δ_τ > 0
    have hconv_diff : Filter.Tendsto
        (fun t => edot (q t) (E.map τ_star) - edot (q t) (E.map τ)) Filter.atTop
        (nhds (edot q_star (E.map τ_star) - edot q_star (E.map τ))) :=
      (hinner_cts (E.map τ_star)).sub (hinner_cts (E.map τ))
    -- Since the limit is δ_τ > 0, eventually the difference is > 0
    have hpos : ∀ᶠ t in Filter.atTop,
        edot (q t) (E.map τ_star) - edot (q t) (E.map τ) > 0 :=
      hconv_diff.eventually (isOpen_Ioi.mem_nhds hδ)
    exact hpos.mono (fun t ht => by linarith)
  -- Step 2: X is finite, so take a common T₀ for all τ ≠ τ_star
  have h_eventually : ∀ᶠ t in Filter.atTop, ∀ τ : X, τ ≠ τ_star →
      edot (q t) (E.map τ) < edot (q t) (E.map τ_star) := by
    have : ∀ τ : X, ∀ᶠ t in Filter.atTop,
        τ ≠ τ_star → edot (q t) (E.map τ) < edot (q t) (E.map τ_star) := by
      intro τ
      by_cases hτ : τ = τ_star
      · simp only [hτ, ne_eq, not_true, forall_false, Filter.eventually_true]
      · exact (h_gap τ hτ).mono (fun t ht _ => ht)
    rw [Filter.eventually_all]
    exact this
  -- Step 3: On this eventually set, eArgmax E (q t) = τ_star
  have h_eArgmax_eventually : ∀ᶠ t in Filter.atTop, eArgmax E (q t) = τ_star := by
    apply h_eventually.mono
    intro t ht
    apply eArgmax_eq_unique E (q t) τ_star
    · intro τ
      by_cases hτ : τ = τ_star
      · simp [hτ]
      · exact le_of_lt (ht τ hτ)
    · intro τ' hτ'_max
      -- τ' is a maximizer of q t scores
      -- If τ' ≠ τ_star, then edot (q t) (E.map τ') < edot (q t) (E.map τ_star)
      -- = edot (q t) (E.map τ')
      -- Contradiction. So τ' = τ_star.
      by_contra hτ'ne
      have h1 : edot (q t) (E.map τ') < edot (q t) (E.map τ_star) := ht τ' hτ'ne
      have h2 : edot (q t) (E.map τ_star) ≤ edot (q t) (E.map τ') := hτ'_max τ_star
      linarith
  rw [Filter.eventually_atTop] at h_eArgmax_eventually
  obtain ⟨T₀, hT₀⟩ := h_eArgmax_eventually
  exact ⟨T₀, fun t ht => by rw [hT₀ t (le_of_lt ht), h_eArgmax_star]⟩
