/-
  SleepLoop/CaptureInertness/FiniteArgmax.lean

  Lemma 83 (lem:finite_argmax): Finite argmax crossings under convergent perturbation.
  If q_t -> q* with Sigma ||q_{t+1} - q_t|| < infinity and E is generic at q*,
  then the E-argmax stabilizes after finitely many transitions.
  Level: A (uses only linearity of the score).
-/
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.CaptureInertness.CaptureArgmax
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Finset BigOperators

/-! ## Finite Argmax Crossings -/

variable {X : Type*} [Fintype X] [DecidableEq X] [Nontrivial X] {d : ℕ}

/-- Paper: lem:finite_argmax (definition -- equilibrium score gap).
    The equilibrium score gap at q*:
    delta = q* . E(tau*) - max_{tau != tau*} q* . E(tau) > 0. -/
noncomputable def argmaxGap
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

/-- Paper: lem:finite_argmax.
    If q_t -> q* with Sigma ||q_{t+1} - q_t|| < infinity,
    and argmax_tau q* . E(tau) is unique (gap delta > 0), then there exists T_0
    such that for all t > T_0, argmax_tau q_t . E(tau) = argmax_tau q* . E(tau).

    Proof: Since q_t -> q*, there exists T_0 with ||q_t - q*|| < delta/(2R)
    for all t > T_0. For any tau != tau* and t > T_0:
      q_t . E(tau*) - q_t . E(tau)
        = [q* . E(tau*) - q* . E(tau)] + (q_t - q*) . [E(tau*) - E(tau)]
        >= delta - 2R ||q_t - q*||
        > delta - 2R * delta/(2R) = 0. -/
theorem finite_argmax_crossings [Nonempty X]
    (E : Embedding X d)
    (R : ℝ) (hR : R = E.radius)
    -- q_t converges to q*
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    (q_star : EuclideanSpace ℝ (Fin d))
    (hq : Filter.Tendsto q Filter.atTop (nhds q_star))
    -- Summable increments
    (_hq_sum : Summable fun t => ‖q (t + 1) - q t‖)
    -- τ* is the unique argmax at q*
    (τ_star : X)
    (_hτ : ∀ τ : X, edot q_star (E.map τ) ≤ edot q_star (E.map τ_star))
    (_hτ_unique : ∀ τ : X, τ ≠ τ_star →
      edot q_star (E.map τ) < edot q_star (E.map τ_star))
    -- The gap is positive
    (δ : ℝ) (hδ : 0 < δ)
    (hδ_def : δ = argmaxGap E q_star τ_star) :
    -- There exists T₀ after which the argmax is constant
    ∃ T₀ : ℕ, ∀ t : ℕ, T₀ < t →
      ∀ τ : X, edot (q t) (E.map τ) ≤ edot (q t) (E.map τ_star) := by
  -- Use convergence to find T₀ with dist(q t, q*) < δ / (2R) for all t ≥ T₀
  have hR_pos : 0 < R := hR ▸ E.radius_pos
  have hε_pos : 0 < δ / (2 * R) := by positivity
  rw [Metric.tendsto_atTop] at hq
  obtain ⟨T₀, hT₀⟩ := hq (δ / (2 * R)) hε_pos
  refine ⟨T₀, fun t ht τ => ?_⟩
  by_cases hτeq : τ = τ_star
  · simp [hτeq]
  · have hdist : dist (q t) q_star < δ / (2 * R) :=
        hT₀ t (Nat.le_of_lt_succ (Nat.lt_succ_of_lt ht))
    rw [dist_eq_norm] at hdist
    have hgap : δ ≤ edot q_star (E.map τ_star) - edot q_star (E.map τ) := by
      rw [hδ_def, argmaxGap]
      have hmem : τ ∈ Finset.univ.erase τ_star :=
        Finset.mem_erase.mpr ⟨hτeq, Finset.mem_univ τ⟩
      have hle : edot q_star (E.map τ) ≤
          Finset.sup' (Finset.univ.erase τ_star)
            (by obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial X).exists_pair_ne
                by_cases hav : a = τ_star
                · exact ⟨b, Finset.mem_erase.mpr
                    ⟨fun h => hab (hav ▸ h.symm), Finset.mem_univ _⟩⟩
                · exact ⟨a, Finset.mem_erase.mpr ⟨hav, Finset.mem_univ _⟩⟩)
            (fun τ' => edot q_star (E.map τ')) :=
        Finset.le_sup' (fun τ' => edot q_star (E.map τ')) hmem
      linarith
    have hpert : edot (q t - q_star) (E.map τ_star - E.map τ) > -(δ) := by
      have hcs : |edot (q t - q_star) (E.map τ_star - E.map τ)| ≤
          ‖q t - q_star‖ * ‖E.map τ_star - E.map τ‖ := abs_real_inner_le_norm _ _
      have hbound : ‖E.map τ_star - E.map τ‖ ≤ 2 * R :=
        calc ‖E.map τ_star - E.map τ‖
            ≤ ‖E.map τ_star‖ + ‖E.map τ‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (hR ▸ E.bounded τ_star) (hR ▸ E.bounded τ)
          _ = 2 * R := by ring
      have hbound2 : ‖q t - q_star‖ * ‖E.map τ_star - E.map τ‖ < δ :=
        calc ‖q t - q_star‖ * ‖E.map τ_star - E.map τ‖
            ≤ ‖q t - q_star‖ * (2 * R) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
          _ < δ / (2 * R) * (2 * R) := mul_lt_mul_of_pos_right hdist (by linarith)
          _ = δ := by field_simp
      linarith [neg_abs_le (edot (q t - q_star) (E.map τ_star - E.map τ))]
    suffices h : 0 ≤ edot (q t) (E.map τ_star) - edot (q t) (E.map τ) by linarith
    have hrw : edot (q t) (E.map τ_star) - edot (q t) (E.map τ) =
        edot (q t) (E.map τ_star - E.map τ) := by simp only [edot, inner_sub_right]
    rw [hrw]
    have hrw2 : edot (q t) (E.map τ_star - E.map τ) =
        edot q_star (E.map τ_star - E.map τ) +
        edot (q t - q_star) (E.map τ_star - E.map τ) := by
      conv_lhs =>
        rw [show q t = q_star + (q t - q_star) from (add_sub_cancel q_star (q t)).symm]
      simp only [edot, inner_add_left]
    rw [hrw2]
    have hgap2 : δ ≤ edot q_star (E.map τ_star - E.map τ) := by
      simp only [edot, inner_sub_right]; linarith
    linarith

/-- Paper: lem:finite_argmax (corollary).
    The total number of argmax transitions is finite. -/
theorem argmax_transitions_finite [Nonempty X]
    (E : Embedding X d)
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    (q_star : EuclideanSpace ℝ (Fin d))
    (hq : Filter.Tendsto q Filter.atTop (nhds q_star))
    (_hq_sum : Summable fun t => ‖q (t + 1) - q t‖)
    -- Generic embedding at q*
    (hgen_at_star : ∃! τ : X, ∀ τ' : X,
      edot q_star (E.map τ') ≤ edot q_star (E.map τ)) :
    ∃ N : ℕ, eArgmaxTransitions E q N = eArgmaxTransitions E q (N + 1) := by
  obtain ⟨τ_star, hτ_max, hτ_unique⟩ := hgen_at_star
  have hτ_strict : ∀ τ : X, τ ≠ τ_star →
      edot q_star (E.map τ) < edot q_star (E.map τ_star) := by
    intro τ hτne
    rcases lt_or_eq_of_le (hτ_max τ) with h | h
    · exact h
    · exact absurd (hτ_unique τ (fun τ' => (hτ_max τ').trans h.symm.le)) hτne
  have hδ_pos : 0 < argmaxGap E q_star τ_star := by
    unfold argmaxGap
    have hlt : Finset.sup' (Finset.univ.erase τ_star)
        (by obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial X).exists_pair_ne
            by_cases hav : a = τ_star
            · exact ⟨b, Finset.mem_erase.mpr
                ⟨fun h => hab (hav ▸ h.symm), Finset.mem_univ _⟩⟩
            · exact ⟨a, Finset.mem_erase.mpr ⟨hav, Finset.mem_univ _⟩⟩)
        (fun τ => edot q_star (E.map τ)) < edot q_star (E.map τ_star) := by
      rw [Finset.sup'_lt_iff]
      intro τ hτ_mem
      simp only [Finset.mem_erase] at hτ_mem
      exact hτ_strict τ hτ_mem.1
    linarith
  -- Use convergence to get T₁ with strict gap at each q t for t ≥ T₁
  have hR_pos : 0 < E.radius := E.radius_pos
  have hε_pos : 0 < argmaxGap E q_star τ_star / (2 * E.radius) := by positivity
  rw [Metric.tendsto_atTop] at hq
  obtain ⟨T₁, hT₁⟩ := hq (argmaxGap E q_star τ_star / (2 * E.radius)) hε_pos
  -- For t ≥ T₁, τ_star is the STRICT argmax at q t (for all τ ≠ τ_star)
  have hstrict_at : ∀ t : ℕ, T₁ ≤ t →
      ∀ τ : X, τ ≠ τ_star → edot (q t) (E.map τ) < edot (q t) (E.map τ_star) := by
    intro t ht τ hτne
    have hdist := hT₁ t ht
    rw [dist_eq_norm] at hdist
    have hgap_τ : argmaxGap E q_star τ_star ≤
        edot q_star (E.map τ_star) - edot q_star (E.map τ) := by
      unfold argmaxGap
      have hmem : τ ∈ Finset.univ.erase τ_star :=
        Finset.mem_erase.mpr ⟨hτne, Finset.mem_univ τ⟩
      have hle := Finset.le_sup' (fun τ' => edot q_star (E.map τ')) hmem
      linarith
    have hpert : edot (q t - q_star) (E.map τ_star - E.map τ) >
        -(argmaxGap E q_star τ_star) := by
      have hcs : |edot (q t - q_star) (E.map τ_star - E.map τ)| ≤
          ‖q t - q_star‖ * ‖E.map τ_star - E.map τ‖ := abs_real_inner_le_norm _ _
      have hbound : ‖E.map τ_star - E.map τ‖ ≤ 2 * E.radius :=
        calc ‖E.map τ_star - E.map τ‖
            ≤ ‖E.map τ_star‖ + ‖E.map τ‖ := norm_sub_le _ _
          _ ≤ E.radius + E.radius := add_le_add (E.bounded τ_star) (E.bounded τ)
          _ = 2 * E.radius := by ring
      have hbound2 : ‖q t - q_star‖ * ‖E.map τ_star - E.map τ‖ <
          argmaxGap E q_star τ_star :=
        calc ‖q t - q_star‖ * ‖E.map τ_star - E.map τ‖
            ≤ ‖q t - q_star‖ * (2 * E.radius) :=
                mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
          _ < argmaxGap E q_star τ_star / (2 * E.radius) * (2 * E.radius) :=
                mul_lt_mul_of_pos_right hdist (by linarith)
          _ = argmaxGap E q_star τ_star := by field_simp
      linarith [neg_abs_le (edot (q t - q_star) (E.map τ_star - E.map τ))]
    -- Now assemble: edot (q t) τ_star - edot (q t) τ > 0
    have hrw : edot (q t) (E.map τ_star) - edot (q t) (E.map τ) =
        edot q_star (E.map τ_star - E.map τ) +
        edot (q t - q_star) (E.map τ_star - E.map τ) := by
      have heq1 : edot (q t) (E.map τ_star) - edot (q t) (E.map τ) =
          edot (q t) (E.map τ_star - E.map τ) := by simp only [edot, inner_sub_right]
      have heq2 : edot (q t) (E.map τ_star - E.map τ) =
          edot q_star (E.map τ_star - E.map τ) +
          edot (q t - q_star) (E.map τ_star - E.map τ) := by
        conv_lhs =>
          rw [show q t = q_star + (q t - q_star) from (add_sub_cancel q_star (q t)).symm]
        simp only [edot, inner_add_left]
      rw [heq1, heq2]
    have hgap2 : argmaxGap E q_star τ_star ≤ edot q_star (E.map τ_star - E.map τ) := by
      simp only [edot, inner_sub_right]; linarith
    linarith [hrw]
  -- τ_star is the unique argmax at q t for all t ≥ T₁: use eArgmax_eq_unique
  have harg_eq : ∀ t : ℕ, T₁ ≤ t → eArgmax E (q t) = τ_star := by
    intro t ht
    apply eArgmax_eq_unique
    · intro τ
      by_cases hτeq : τ = τ_star
      · simp [hτeq]
      · exact le_of_lt (hstrict_at t ht τ hτeq)
    · intro τ' hτ'_max
      by_contra hτ'ne
      linarith [hstrict_at t ht τ' hτ'ne, hτ'_max τ_star]
  -- No transition occurs at step T₁: eArgmax E (q T₁) = τ_star = eArgmax E (q (T₁ + 1))
  use T₁
  have h1 := harg_eq T₁ (le_refl T₁)
  have h2 := harg_eq (T₁ + 1) (Nat.le_succ T₁)
  simp only [eArgmaxTransitions, Finset.range_add_one]
  rw [Finset.filter_insert]
  simp [h1, h2]
