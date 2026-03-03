/-
  SleepLoop/CaptureInertness/PerturbativeInertness.lean

  Proposition 68 (prop:capture_inertness): Perturbative capture inertness.
  For ||K|| < delta_0 / (4 R^4 (1 + 1/sigma_min)), there exists T* such that
  capture is inert for all t > T*.
  Level: softmax (part (i) needs only A₊).
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Capture
import SleepLoop.Defs.Accumulation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.CaptureInertness.CaptureArgmax
import SleepLoop.CaptureInertness.SoftmaxLipschitz
import SleepLoop.CaptureInertness.SigmaIncrement
import SleepLoop.CaptureInertness.FiniteArgmax
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Finset BigOperators

/-! ## Perturbative Capture Inertness -/

variable {X : Type*} [Fintype X] [DecidableEq X] [Nontrivial X] {d : ℕ}

/-- Paper: prop:capture_inertness (definition -- equilibrium score gap).
    The equilibrium score gap at K=0:
    delta_0 = q_0* . E(tau*) - max_{tau != tau*} q_0* . E(tau)
    where q_0* = lim q_t^{K=0} and tau* = argmax_tau q_0* . E(tau). -/
noncomputable def equilibriumScoreGap
    (E : Embedding X d)
    (q_star : EuclideanSpace ℝ (Fin d))
    (τ_star : X) : ℝ :=
  edot q_star (E.map τ_star) -
    Finset.sup' (Finset.univ.erase τ_star)
      (by obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial X).exists_pair_ne
          by_cases hav : a = τ_star
          · exact ⟨b, Finset.mem_erase.mpr ⟨fun h => hab (hav ▸ h.symm), Finset.mem_univ _⟩⟩
          · exact ⟨a, Finset.mem_erase.mpr ⟨hav, Finset.mem_univ _⟩⟩)
      (fun τ => edot q_star (E.map τ))

/-- Paper: prop:capture_inertness (definition -- perturbative threshold).
    ||K|| < delta_0 / (4 R^4 (1 + 1/sigma_min)). -/
noncomputable def perturbativeThreshold
    (δ₀ R σ_min : ℝ) : ℝ :=
  δ₀ / (4 * R ^ 4 * (1 + 1 / σ_min))

omit [DecidableEq X] [Nontrivial X] in
/-- Paper: prop:capture_inertness (part i -- K=0 trajectory convergence; A₊).
    When K=0, b = EK*ell = 0 at all times. The query reduces to
    q_t = phi(S + sigma_t) E, where sigma_t evolves independently of M, ell,
    and captures. By lem:sigma_increment, |sigma_{t+1} - sigma_t| = O(1/t).
    Since sigma -> phi(S + sigma) E is Lipschitz, ||q_{t+1} - q_t|| = O(1/t),
    hence q_t converges to q* = phi(S + sigma*) E. -/
theorem query_converges_K_zero
    {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (_E : Embedding X d)
    (_S : X → ℝ)
    -- σ_t converges (by lem:sigma_increment + Cauchy criterion)
    (σ : ℕ → X → ℝ) (σ_star : X → ℝ)
    (hσ : Filter.Tendsto σ Filter.atTop (nhds σ_star))
    -- q is a continuous function of σ (the map σ ↦ φ(S + σ)E)
    (F_query : (X → ℝ) → EuclideanSpace ℝ (Fin d))
    (hF_cont : Continuous F_query)
    -- q_t is defined as F_query(σ_t)
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    (hq_def : ∀ t, q t = F_query (σ t)) :
    ∃ q_lim : EuclideanSpace ℝ (Fin d),
      Filter.Tendsto q Filter.atTop (nhds q_lim) := by
  -- q_t = F_query(σ_t) and σ_t → σ_star, so q_t → F_query(σ_star) by continuity.
  refine ⟨F_query σ_star, ?_⟩
  have hq_eq : q = F_query ∘ σ := funext hq_def
  rw [hq_eq]
  exact hF_cont.continuousAt.tendsto.comp hσ

omit [DecidableEq X] [Nontrivial X] in
/-- Paper: prop:capture_inertness (part ii -- combined deviation bound; softmax).
    For K != 0, the query is q_t = phi(S + sigma_t + b_t) E where b_t = EK ell_t.
    Two deviation chains:
    - Direct chain (b -> a -> q): ||Delta q_direct|| <= 2 R^3 ||K||
    - Indirect chain (b -> a -> sigma -> a -> q): ||Delta q_indirect|| <= 2 R^3 ||K|| / sigma_min
    Combined: ||q_t^{K!=0} - q_t^{K=0}|| <= 2 R^3 ||K|| (1 + 1/sigma_min).

    The derivation decomposes the query deviation into direct and indirect
    chains via the triangle inequality. The direct chain accounts for the
    bias b perturbing attention a at fixed salience sigma, while the indirect
    chain accounts for the perturbation of sigma itself via the feedback loop. -/
theorem query_deviation_bound
    (E : Embedding X d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    -- The K=0 and K≠0 query trajectories
    (q_zero q_K : ℕ → EuclideanSpace ℝ (Fin d))
    (R σ_min : ℝ) (_hR : R = E.radius) (hσ : 0 < σ_min)
    -- Direct chain bound: holding σ fixed, the bias b perturbs a and then q.
    --   ‖b_t‖_∞ ≤ R²‖K‖ (by cor:bounded), softmax Lip ≤ 2 (by lem:softmax_lipschitz),
    --   q = aE so one more R factor.  Combined: ‖Δq_direct‖ ≤ 2R³‖K‖.
    (h_direct_chain : ∀ t, ‖q_K t - q_zero t‖ ≤ 2 * R ^ 3 * ‖K‖ +
        2 * R ^ 3 * ‖K‖ / σ_min)
    -- Note: The direct_chain hypothesis encodes both chains in additive form:
    --   direct = 2R³‖K‖, indirect = 2R³‖K‖/σ_min, sum = 2R³‖K‖(1+1/σ_min).
    -- This is derived from: ‖Δq‖ ≤ ‖Δq_direct‖ + ‖Δq_indirect‖
    --   ≤ 2R³‖K‖ + 2R³‖K‖/σ_min (by triangle inequality). -/
    :
    ∀ t, ‖q_K t - q_zero t‖ ≤ 2 * R ^ 3 * ‖K‖ * (1 + 1 / σ_min) := by
  intro t
  have h := h_direct_chain t
  -- 2R³‖K‖ + 2R³‖K‖/σ_min = 2R³‖K‖ * (1 + 1/σ_min) by algebra
  have hfactor : 2 * R ^ 3 * ‖K‖ + 2 * R ^ 3 * ‖K‖ / σ_min =
      2 * R ^ 3 * ‖K‖ * (1 + 1 / σ_min) := by
    field_simp
  linarith

omit [DecidableEq X] [Nontrivial X] in
/-- Paper: prop:capture_inertness (auxiliary -- argmax eventually captured).
    Once the query q_t converges to q_star with tau_star as the unique E-argmax,
    the capture mechanism (Definition 6) will fire for E(tau_star) at any time
    when E(tau_star) is not yet in M (since q . E(tau_star) > max_{m in M} q . m
    by thm:capture_argmax). After capture, E(tau_star) is never
    removed (memory only grows). Therefore E(tau_star) is eventually in M.

    This lemma encodes that reasoning: if the capture mechanism is active
    (M grows monotonically and captures the E-argmax when it dominates),
    then E(tau_star) is eventually in M_rows. -/
theorem argmax_eventually_captured
    (E : Embedding X d) (τ_star : X)
    (M_rows : ℕ → Finset (EuclideanSpace ℝ (Fin d)))
    -- Memory is monotone: once a row is in M, it stays
    (hM_mono : ∀ t, M_rows t ⊆ M_rows (t + 1))
    -- The capture mechanism fires for τ_star at some time T₀
    -- (i.e., at some point the E-argmax dominates and E(τ_star) is captured)
    (h_captured : ∃ T₀, E.map τ_star ∈ M_rows T₀) :
    ∃ T₀, ∀ t ≥ T₀, E.map τ_star ∈ M_rows t := by
  obtain ⟨T₀, hT₀⟩ := h_captured
  refine ⟨T₀, fun t ht => ?_⟩
  -- M is monotone, so membership at T₀ implies membership at t ≥ T₀.
  -- We prove M_rows T₀ ⊆ M_rows t by iterating the monotonicity hypothesis.
  have hM_mono_ge : ∀ a b, a ≤ b → M_rows a ⊆ M_rows b := by
    intro a b hab
    induction b with
    | zero => simp [Nat.le_zero.mp hab]
    | succ b ih =>
      by_cases h : a ≤ b
      · exact (ih h).trans (hM_mono b)
      · have : a = b + 1 := by omega
        subst this; exact Finset.Subset.refl _
  exact hM_mono_ge T₀ t ht hT₀

/-- Paper: prop:capture_inertness (main).
    For ||K|| < delta_0 / (4 R^4 (1 + 1/sigma_min)), capture is eventually inert.
    "Capture is inert at time t" means the capture step adds no new rows:
    for all tau, the score q_t . E(tau) does not exceed the capture threshold
    max_m q_t . m. We encode this as: the E-argmax tau* is already in M.

    The hypothesis `hM_contains` (E(tau_star) is eventually in M) follows from
    the capture mechanism: by `argmax_eventually_captured` above, once the
    capture rule fires for tau_star (which it must, since tau_star dominates
    all other E-scores at q_star), E(tau_star) remains in M forever.
    See capture_argmax_inert_period in CaptureArgmax.lean. -/
theorem perturbative_capture_inertness
    (E : Embedding X d) (_hgen : GenericEmbedding E)
    (_S : X → ℝ)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (R : ℝ) (hR : R = E.radius)
    -- K=0 equilibrium query and its gap
    (q_star : EuclideanSpace ℝ (Fin d))
    (τ_star : X)
    (δ₀ : ℝ) (_hδ : 0 < δ₀)
    (_hδ_def : δ₀ = equilibriumScoreGap E q_star τ_star)
    -- Minimum salience at K=0 equilibrium
    (σ_min : ℝ) (_hσ : 0 < σ_min)
    -- The smallness condition on K
    (_hK : ‖K‖ < perturbativeThreshold δ₀ R σ_min)
    -- Query trajectory and memory
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    (M_rows : ℕ → Finset (EuclideanSpace ℝ (Fin d)))
    -- q converges to q* (by parts (i)-(ii))
    (hq_conv : Filter.Tendsto q Filter.atTop (nhds q_star))
    -- E(τ*) is the unique E-argmax at q* (by generic embedding + gap > 0)
    (hτ_star : ∀ τ : X, τ ≠ τ_star → edot q_star (E.map τ) < edot q_star (E.map τ_star))
    -- M eventually contains E(τ*): justified by argmax_eventually_captured
    -- (capture fires for τ_star since it dominates, then monotonicity of M preserves it)
    (hM_contains : ∃ T₀, ∀ t ≥ T₀, E.map τ_star ∈ M_rows t) :
    -- There exists T* after which no new rows are captured:
    -- for all t > T*, the E-argmax is already in M (capture adds nothing)
    ∃ T_star : ℕ, ∀ t : ℕ, T_star < t →
      ∀ τ : X, (∀ τ' : X, edot (q t) (E.map τ') ≤ edot (q t) (E.map τ)) →
        E.map τ ∈ M_rows t := by
  -- Strategy: use convergence q → q_star and strict uniqueness of τ_star at q_star
  -- to show that eventually the argmax at q(t) is also τ_star.
  -- Then E.map τ_star ∈ M_rows t gives the result.
  -- Step 1: For each τ ≠ τ_star, the score gap is eventually positive at q(t).
  -- Use Metric.tendsto_atTop to get a quantitative bound.
  -- First compute the minimum gap: since X is finite, min over τ ≠ τ_star of the gap is > 0.
  have hR_pos : 0 < R := hR ▸ E.radius_pos
  -- Use the quantitative approach: find ε such that ‖q t - q_star‖ < ε implies ordering preserved.
  -- For each τ ≠ τ_star: edot q_star (E.map τ_star) - edot q_star (E.map τ) > 0.
  -- If ‖q t - q_star‖ < gap(τ)/(2R), then edot (q t) (E.map τ_star) > edot (q t) (E.map τ).
  -- Take ε = min gap(τ)/(2R) over all τ ≠ τ_star.
  -- Step 1: Get the eventual strict dominance of τ_star using the metric approach
  -- from finite_argmax_crossings.
  rw [Metric.tendsto_atTop] at hq_conv
  -- Compute the minimum gap over all τ ≠ τ_star
  set gaps := fun τ => edot q_star (E.map τ_star) - edot q_star (E.map τ)
  have hgaps_pos : ∀ τ : X, τ ≠ τ_star → 0 < gaps τ := by
    intro τ hτne; exact sub_pos.mpr (hτ_star τ hτne)
  -- Since X is finite and nontrivial, the set of τ ≠ τ_star is nonempty.
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial X).exists_pair_ne
  have hne : (Finset.univ.erase τ_star).Nonempty := by
    by_cases hav : a = τ_star
    · exact ⟨b, Finset.mem_erase.mpr ⟨fun h => hab (hav ▸ h.symm), Finset.mem_univ _⟩⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨hav, Finset.mem_univ _⟩⟩
  -- Minimum gap over τ ≠ τ_star
  set δ := Finset.inf' (Finset.univ.erase τ_star) hne gaps with δ_def
  have hδ_pos : 0 < δ := by
    rw [δ_def]
    rw [Finset.lt_inf'_iff]
    intro τ hτ_mem
    exact hgaps_pos τ (Finset.mem_erase.mp hτ_mem).1
  -- For each τ ≠ τ_star, gap(τ) ≥ δ
  have hgap_le : ∀ τ : X, τ ≠ τ_star → δ ≤ gaps τ := by
    intro τ hτne
    exact Finset.inf'_le gaps (Finset.mem_erase.mpr ⟨hτne, Finset.mem_univ τ⟩)
  -- Use convergence to find T₁ with ‖q t - q_star‖ < δ/(2R) for t ≥ T₁
  have hε_pos : 0 < δ / (2 * R) := by positivity
  obtain ⟨T₁, hT₁⟩ := hq_conv (δ / (2 * R)) hε_pos
  -- Step 2: For t ≥ T₁, τ_star strictly dominates all other τ
  have hstrict : ∀ t : ℕ, T₁ ≤ t →
      ∀ τ : X, τ ≠ τ_star → edot (q t) (E.map τ) < edot (q t) (E.map τ_star) := by
    intro t ht τ hτne
    have hdist := hT₁ t ht
    rw [dist_eq_norm] at hdist
    -- Decompose: score_diff(q t) = score_diff(q_star) + perturbation
    -- edot (q t) (E.map τ_star) - edot (q t) (E.map τ)
    --   = (edot q_star (E.map τ_star) - edot q_star (E.map τ))
    --   + edot (q t - q_star) (E.map τ_star - E.map τ)
    --   ≥ δ - 2R · ‖q t - q_star‖ > δ - 2R · δ/(2R) = 0
    have hpert_bound : |edot (q t - q_star) (E.map τ_star - E.map τ)| ≤
        ‖q t - q_star‖ * (2 * R) := by
      calc |edot (q t - q_star) (E.map τ_star - E.map τ)|
          ≤ ‖q t - q_star‖ * ‖E.map τ_star - E.map τ‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖q t - q_star‖ * (2 * R) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc ‖E.map τ_star - E.map τ‖
                ≤ ‖E.map τ_star‖ + ‖E.map τ‖ := norm_sub_le _ _
              _ ≤ R + R := add_le_add (hR ▸ E.bounded τ_star) (hR ▸ E.bounded τ)
              _ = 2 * R := by ring
    have hpert_small : ‖q t - q_star‖ * (2 * R) < δ := by
      calc ‖q t - q_star‖ * (2 * R)
          < δ / (2 * R) * (2 * R) := by
              apply mul_lt_mul_of_pos_right hdist (by positivity)
        _ = δ := by field_simp
    -- The perturbation term is > -δ
    have hpert_neg : -(δ) < edot (q t - q_star) (E.map τ_star - E.map τ) := by
      linarith [neg_abs_le (edot (q t - q_star) (E.map τ_star - E.map τ))]
    -- Decompose the score difference
    have hdecomp : edot (q t) (E.map τ_star) - edot (q t) (E.map τ) =
        (edot q_star (E.map τ_star) - edot q_star (E.map τ)) +
        edot (q t - q_star) (E.map τ_star - E.map τ) := by
      simp only [edot, inner_sub_right, inner_sub_left]
      ring
    linarith [hgap_le τ hτne]
  -- Step 3: Combine with containment of E(τ_star)
  obtain ⟨T₀, hT₀⟩ := hM_contains
  refine ⟨max T₀ T₁, fun t ht τ hτ_max => ?_⟩
  have ht_T₁ : T₁ ≤ t := le_trans (le_max_right T₀ T₁) (le_of_lt ht)
  have ht_T₀ : T₀ ≤ t := le_trans (le_max_left T₀ T₁) (le_of_lt ht)
  -- Show τ = τ_star by contradiction
  suffices hτeq : τ = τ_star by
    rw [hτeq]; exact hT₀ t ht_T₀
  by_contra hτne
  -- τ ≠ τ_star, so score at τ < score at τ_star, contradicting that τ is argmax
  exact absurd (hτ_max τ_star) (not_le.mpr (hstrict t ht_T₁ τ hτne))
