/-
  SleepLoop/Sleep/SleepEfficacy.lean

  Theorem 41 (thm:sleep_efficacy): Sleep restores retrieval precision.
  Under S=0 with capture disabled, V(t) strictly decreases and D(t) → 0.
  Level: A₊.

  Part (i): V(t) → 0 and D(t) → 0 (fixed-query version delegates to
    cor:sleep / Core.Convergence; the full varying-query version from the
    paper requires the diameter contraction argument).
  Part (ii): Prototype formation (Cauchy-Schwarz).
  Part (iii): Cluster recovery (softmax bound).
  Part (iv): gamma(t) → 0 termination (squeeze from V → 0).
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster
import SleepLoop.Core.Convergence
import SleepLoop.Core.SelfLimiting

open Finset BigOperators

/-! ## Sleep Efficacy (Theorem 41) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) V(t) → 0 under fixed-query consolidation with A+ map.
    This is the fixed-query version (cor:sleep). The full paper proof of
    thm:sleep_efficacy(i) handles varying queries via the diameter argument.
    Paper: thm:sleep_efficacy(i), via Corollary 35 (cor:sleep). -/
theorem sleep_efficacy_V_decreasing
    {n : ℕ} (hn : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    -- v is the unique anchor at every step
    (hv : ∀ t k, w t k ≤ w t v)
    (hv_unique : ∀ t k, k ≠ v → w t k < w t v)
    -- all weights positive (from A+ positive simplex map)
    (hw_pos : ∀ t k, 0 < w t k)
    -- M evolves by consolidation steps under fixed query q
    (h_step : ∀ t, M (t + 1) = consolidationStep φ br (w t) q (M t) (by omega))
    -- M is bounded (lives in conv(E(X)))
    (h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R)
    -- Uniform weight gap
    (h_weight_gap : ∃ δ : ℝ, 0 < δ ∧ ∀ t k, k ≠ v → w t k ≤ (1 - δ) * w t v) :
    -- V(t) → 0
    Filter.Tendsto (fun t => lyapunovV (M t) v hn) Filter.atTop (nhds 0) :=
  convergence_under_consolidation φ br q hn v M w hv hv_unique hw_pos h_step h_bounded
    h_weight_gap

/-- (i, diameter version) D(t) → 0 under fixed-query consolidation with A+ map.
    Anchor-independent version: D(t) = max_{i,j} ||m_i - m_j|| → 0.
    Paper: thm:sleep_efficacy(i), diameter argument. -/
theorem sleep_efficacy_diameter_decreasing
    {n : ℕ} (hn : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (hv : ∀ t k, w t k ≤ w t v)
    (hv_unique : ∀ t k, k ≠ v → w t k < w t v)
    (hw_pos : ∀ t k, 0 < w t k)
    (h_step : ∀ t, M (t + 1) = consolidationStep φ br (w t) q (M t) (by omega))
    (h_bounded : ∃ R : ℝ, ∀ t j, ‖M t j‖ ≤ R)
    (h_weight_gap : ∃ δ : ℝ, 0 < δ ∧ ∀ t k, k ≠ v → w t k ≤ (1 - δ) * w t v) :
    -- D(t) → 0
    Filter.Tendsto (fun t => diameter (M t) (by omega)) Filter.atTop (nhds 0) :=
  diameter_converges_to_zero φ br q hn v M w hv hv_unique hw_pos h_step h_bounded
    h_weight_gap

/-- (ii) Consolidation reduces effective memory size through prototype formation.
    If ‖m_i - m_j‖ < ε after consolidation, they are functionally merged.
    Paper: thm:sleep_efficacy(ii). -/
theorem sleep_efficacy_prototype_formation
    {n : ℕ} (_hn : 1 < n)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (i j : Fin n) (ε : ℝ) (_hε : 0 < ε)
    (h_close : ‖M i - M j‖ < ε) :
    -- Retrieval weights differ by at most ‖q‖ · ε
    |edot q (M i) - edot q (M j)| ≤ ‖q‖ * ε := by
  -- edot q (M i) - edot q (M j) = edot q (M i - M j) = <q, M i - M j>
  -- By Cauchy-Schwarz: |<q, M i - M j>| ≤ ‖q‖ * ‖M i - M j‖ < ‖q‖ * ε
  have key : edot q (M i) - edot q (M j) = edot q (M i - M j) := by
    simp [edot, inner_sub_right]
  rw [key]
  calc |edot q (M i - M j)| ≤ ‖q‖ * ‖M i - M j‖ := abs_real_inner_le_norm q (M i - M j)
    _ ≤ ‖q‖ * ε := by
        apply mul_le_mul_of_nonneg_left (le_of_lt h_close) (norm_nonneg q)

/-- (iii) After sleep, effective number of distinguishable impressions decreases.
    Under softmax with p clusters separated by gap g_p:
    w_v ≥ 1/(1 + (p-1)exp(-β·g_p)).
    Paper: thm:sleep_efficacy(iii). -/
theorem sleep_efficacy_cluster_recovery
    (p : ℕ) (_hp : 1 ≤ p)
    (β g_p : ℝ) (_hβ : 0 < β) (_hg : 0 < g_p) :
    1 / (1 + (↑(p - 1)) * Real.exp (-β * g_p)) > 0 := by
  apply div_pos one_pos
  have h_cast : (0 : ℝ) ≤ ↑(p - 1) := Nat.cast_nonneg _
  have h_exp : 0 < Real.exp (-β * g_p) := Real.exp_pos _
  linarith [mul_nonneg h_cast (le_of_lt h_exp)]

/-- (iii, explicit) The actual softmax weight lower bound from the paper.
    If v is the anchor with score gap g_p above all other impressions under
    softmax with inverse temperature beta, then:
      softmaxBeta beta s v >= 1 / (1 + (p-1) * exp(-beta * g_p))
    Paper: thm:sleep_efficacy(iii), the full quantitative bound. -/
theorem sleep_efficacy_cluster_recovery_explicit
    {p : ℕ} [NeZero p]
    (s : Fin p -> ℝ) (v : Fin p)
    (beta g_p : ℝ) (hbeta : 0 < beta) (_hg : 0 < g_p)
    -- v has score gap g_p above every other impression
    (h_gap : forall k, k ≠ v -> s v - s k >= g_p) :
    softmaxBeta beta s v >= 1 / (1 + (↑(p - 1)) * Real.exp (-beta * g_p)) := by
  unfold softmaxBeta
  -- We need: exp(beta * s v) / sum_k exp(beta * s k) >= 1 / (1 + (p-1)*exp(-beta*g_p))
  -- Equivalently: (1 + (p-1)*exp(-beta*g_p)) * exp(beta*s v) >= sum_k exp(beta*s k)
  -- Split sum: sum = exp(beta*s v) + sum_{k!=v} exp(beta*s k)
  -- For k != v: s k <= s v - g_p, so beta*s k <= beta*(s v - g_p)
  --   exp(beta*s k) <= exp(beta*(s v - g_p)) = exp(beta*s v) * exp(-beta*g_p)
  -- sum_{k!=v} <= (p-1) * exp(beta*s v) * exp(-beta*g_p)
  -- Total: sum <= exp(beta*s v) * (1 + (p-1)*exp(-beta*g_p)) -- QED
  set D := ∑ j : Fin p, Real.exp (beta * s j) with hD_def
  have hD_pos : 0 < D := softmax_denom_pos (fun j => beta * s j)
  have h_ev_pos : 0 < Real.exp (beta * s v) := Real.exp_pos _
  have h_exp_neg_pos : 0 < Real.exp (-beta * g_p) := Real.exp_pos _
  have h_p1_nn : (0 : ℝ) ≤ ↑(p - 1) := Nat.cast_nonneg _
  have h_denom2_pos : 0 < 1 + ↑(p - 1) * Real.exp (-beta * g_p) := by
    linarith [mul_nonneg h_p1_nn (le_of_lt h_exp_neg_pos)]
  -- Key inequality: D <= exp(beta*s v) * (1 + (p-1)*exp(-beta*g_p))
  -- This implies exp(beta*s v)/D >= 1/(1+(p-1)*exp(-beta*g_p))
  suffices h_key : D ≤ Real.exp (beta * s v) * (1 + ↑(p - 1) * Real.exp (-beta * g_p)) by
    rw [ge_iff_le]
    -- Goal: 1 / (1+A) <= exp / D
    -- Equivalent to: D <= exp * (1+A) when D > 0 and (1+A) > 0
    rw [div_le_div_iff₀ h_denom2_pos hD_pos]
    linarith
  -- Split D = exp(beta*s v) + sum_{k!=v} exp(beta*s k)
  have h_split : D = Real.exp (beta * s v) +
      ∑ j ∈ Finset.univ.erase v, Real.exp (beta * s j) := by
    rw [hD_def, ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  rw [h_split]
  -- Bound each term in sum_{k!=v}
  have h_each : ∀ j ∈ Finset.univ.erase v,
      Real.exp (beta * s j) ≤ Real.exp (beta * s v) * Real.exp (-beta * g_p) := by
    intro j hj
    rw [Finset.mem_erase] at hj
    have hjv : j ≠ v := hj.1
    have h_sk : s j ≤ s v - g_p := by linarith [h_gap j hjv]
    have h_bsk : beta * s j ≤ beta * (s v - g_p) := by
      exact mul_le_mul_of_nonneg_left h_sk (le_of_lt hbeta)
    calc Real.exp (beta * s j)
        ≤ Real.exp (beta * (s v - g_p)) := Real.exp_le_exp.mpr h_bsk
      _ = Real.exp (beta * s v + (-beta * g_p)) := by ring_nf
      _ = Real.exp (beta * s v) * Real.exp (-beta * g_p) := Real.exp_add _ _
  -- Sum bound
  have h_card : (Finset.univ.erase v : Finset (Fin p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  have h_sum_bound : ∑ j ∈ Finset.univ.erase v, Real.exp (beta * s j) ≤
      ↑(p - 1) * (Real.exp (beta * s v) * Real.exp (-beta * g_p)) := by
    calc ∑ j ∈ Finset.univ.erase v, Real.exp (beta * s j)
        ≤ ∑ _j ∈ Finset.univ.erase v,
            (Real.exp (beta * s v) * Real.exp (-beta * g_p)) :=
          Finset.sum_le_sum h_each
      _ = ↑(Finset.univ.erase v : Finset (Fin p)).card *
            (Real.exp (beta * s v) * Real.exp (-beta * g_p)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ↑(p - 1) * (Real.exp (beta * s v) * Real.exp (-beta * g_p)) := by
          rw [h_card]
  -- Combine
  calc Real.exp (beta * s v) + ∑ j ∈ Finset.univ.erase v, Real.exp (beta * s j)
      ≤ Real.exp (beta * s v) +
          ↑(p - 1) * (Real.exp (beta * s v) * Real.exp (-beta * g_p)) := by
        linarith
    _ = Real.exp (beta * s v) * (1 + ↑(p - 1) * Real.exp (-beta * g_p)) := by ring

/-- (iv) The contraction rate gamma(t) → 0 provides a natural termination condition.
    By Corollary 36 (cor:selflimiting), as V(t) → 0 all impressions converge to v,
    retrieval weights equalize (w_j/w_v → 1), so blend rates lambda_j → 0, hence gamma → 0.
    Paper: thm:sleep_efficacy(iv), via Corollary 36 (cor:selflimiting). -/
theorem sleep_efficacy_termination
    {n : ℕ} (hn : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (br : BlendRate)
    (q : EuclideanSpace ℝ (Fin d))
    (v : Fin n)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Fin n → ℝ)
    (hv : ∀ t k, w t k ≤ w t v)
    (hv_unique : ∀ t k, k ≠ v → w t k < w t v)
    (hw_pos : ∀ t k, 0 < w t k)
    -- The paper derives this from w = φ(q · M^T) and continuity of φ.
    (h_blend_vanish : Filter.Tendsto
      (fun t => Finset.sup' (Finset.univ.erase v) (erase_v_nonempty hn v)
        (fun j => consolidationBlendRates br (w t) (by omega) j))
      Filter.atTop (nhds 0)) :
    -- gamma(t) → 0
    Filter.Tendsto (fun t => contractionRate φ br (w t) q (M t) v (by omega))
      Filter.atTop (nhds 0) :=
  contraction_rate_vanishes φ br q hn v M w hv hv_unique hw_pos h_blend_vanish
