/-
  SleepLoop/CaptureInertness/SigmaIncrement.lean

  Lemma 82 (lem:sigma_increment): Accumulation increment bound.
  Under A₊ with bounded inputs, |sigma_{t+1}(tau) - sigma_t(tau)| = O(1/t).
  The implied constant depends on alpha and N_0 but not on {a_t}.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Accumulation
import SleepLoop.Defs.LoopState
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Compactness.Compact

open Finset BigOperators Filter

/-! ## Accumulation Increment Bound -/

variable {X : Type*} [Fintype X]

/-- Paper: lem:sigma_increment (preamble -- attention bounded away from 0 and 1).
    Under A₊ with bounded inputs and n >= 2, attention is bounded
    away from 0 and 1: a_t(tau) in [alpha, 1-alpha] for some alpha > 0.

    Requires n >= 2 because for n = 1, phi = 1 (only one simplex component),
    making the upper bound phi <= 1 - alpha impossible for alpha > 0.

    Also requires continuity of phi to get a uniform lower bound over all t:
    phi maps the compact set of bounded inputs to a compact subset of the
    open simplex (since phi is positive). The minimum over this compact image
    gives the uniform alpha.

    Paper gap: n >= 2 and continuity are implicit assumptions in the paper's
    "guaranteed by positivity of phi with bounded inputs" claim. -/
theorem attention_bounded_away
    {n : ℕ} (hn : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (hφ_cont : Continuous φ)
    (scores : ℕ → Fin n → ℝ)
    -- Scores are bounded
    (h_bdd : ∃ B : ℝ, ∀ t i, |scores t i| ≤ B) :
    ∃ α : ℝ, 0 < α ∧ ∀ t i, α ≤ φ (scores t) i ∧ φ (scores t) i ≤ 1 - α := by
  -- Extract the bound B
  obtain ⟨B, hB⟩ := h_bdd
  -- We may assume B ≥ 0 (wlog, since |scores t i| ≤ B implies |scores t i| ≤ max B 0)
  set B' := max B 0 with B'_def
  have hB'_nn : 0 ≤ B' := le_max_right B 0
  have hB'_bound : ∀ t i, |scores t i| ≤ B' := fun t i =>
    le_trans (hB t i) (le_max_left B 0)
  -- Define the compact box {x : Fin n → ℝ | ∀ i, x i ∈ [-B', B']}
  set box := Set.pi Set.univ (fun (_ : Fin n) => Set.Icc (-B') B') with box_def
  -- The box is compact (product of compact intervals)
  have hbox_compact : IsCompact box :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  -- n ≥ 2 implies n ≥ 1, so Fin n is nonempty
  have hn_pos : 0 < n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  -- The box is nonempty (0 is in it since B' ≥ 0)
  have hbox_nonempty : box.Nonempty :=
    ⟨0, fun i _ => by simp only [Pi.zero_apply, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩⟩
  -- Each component φ(·) i is continuous
  have hφi_cont : ∀ i : Fin n, Continuous (fun x => φ x i) := by
    intro i; exact (continuous_apply i).comp hφ_cont
  -- Each φ x i > 0
  have hφi_pos : ∀ (x : Fin n → ℝ) (i : Fin n), 0 < φ x i :=
    fun x i => PositiveSimplexMap.pos x i
  -- For each i, find the minimum of φ(·) i on the compact box
  have hφi_min : ∀ i : Fin n, ∃ x₀ ∈ box, ∀ x ∈ box, φ x₀ i ≤ φ x i := by
    intro i
    exact hbox_compact.exists_isMinOn hbox_nonempty (hφi_cont i).continuousOn
  -- Collect minima
  choose x₀ hx₀_mem hx₀_min using hφi_min
  set αs := fun i => φ (x₀ i) i with αs_def
  have hαs_pos : ∀ i, 0 < αs i := fun i => hφi_pos (x₀ i) i
  -- Take α = inf of αs over Fin n
  set α := Finset.inf' Finset.univ Finset.univ_nonempty αs with α_def
  -- We need α to also satisfy the upper bound φ ≤ 1 - α.
  -- Since n ≥ 2 and each component ≥ α, for any i:
  --   φ x i = 1 - Σ_{j≠i} φ x j ≤ 1 - (n-1)·α ≤ 1 - α.
  -- But we need α small enough that 1 - α is a valid upper bound.
  -- Actually, α ≤ αs i ≤ φ(x₀ i) i ≤ 1, and with n ≥ 2 each term ≤ 1 - α
  -- is automatic from the simplex constraint.
  refine ⟨α, ?_, ?_⟩
  · -- α > 0: inf of positive values over nonempty finite set is positive
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty αs
    rw [α_def, hj]; exact hαs_pos j
  · -- The bound
    intro t i
    -- Show scores t is in the box
    have hscores_in_box : scores t ∈ box := by
      intro j _
      simp only [Set.mem_Icc]
      exact ⟨neg_le_of_abs_le (hB'_bound t j), le_of_abs_le (hB'_bound t j)⟩
    constructor
    · -- Lower bound: α ≤ φ (scores t) i
      calc α ≤ αs i := Finset.inf'_le _ (Finset.mem_univ i)
        _ ≤ φ (scores t) i := hx₀_min i (scores t) hscores_in_box
    · -- Upper bound: φ (scores t) i ≤ 1 - α
      -- From simplex sum: φ(scores t) i + Σ_{j≠i} φ(scores t) j = 1
      have hsum := SimplexMap.sum_one (φ := φ) (scores t)
      -- φ(scores t) i = 1 - Σ_{j≠i} φ(scores t) j
      have herase_sum : φ (scores t) i + ∑ j ∈ Finset.univ.erase i, φ (scores t) j =
          ∑ j : Fin n, φ (scores t) j := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      -- Since n ≥ 2, there exists j ≠ i
      have h_card : 1 < (Finset.univ : Finset (Fin n)).card := by
        simp [Finset.card_univ, Fintype.card_fin]; omega
      have h_univ_nontrivial : (Finset.univ : Finset (Fin n)).Nontrivial :=
        Finset.one_lt_card.mp h_card
      have h_erase_nonempty := h_univ_nontrivial.erase_nonempty (a := i)
      obtain ⟨j, hj_in_erase⟩ := h_erase_nonempty
      have hφj_ge_α : α ≤ φ (scores t) j := by
        calc α ≤ αs j := Finset.inf'_le _ (Finset.mem_univ j)
          _ ≤ φ (scores t) j := hx₀_min j (scores t) hscores_in_box
      have herase_ge_α : α ≤ ∑ k ∈ Finset.univ.erase i, φ (scores t) k := by
        calc α ≤ φ (scores t) j := hφj_ge_α
          _ ≤ ∑ k ∈ Finset.univ.erase i, φ (scores t) k :=
            Finset.single_le_sum (fun k _ => le_of_lt (hφi_pos (scores t) k)) hj_in_erase
      -- φ(scores t) i = 1 - Σ_{j≠i} φ(scores t) j ≤ 1 - α
      linarith [hsum]

/-- Paper: lem:sigma_increment (part i -- cumulative attention growth).
    Cumulative attention C_t grows as Theta(t).
    Uses the LINEAR recurrence C(t+1) = C(t) + a(t)*(t+1)/C(t).
    Lower bound: C(t) >= sqrt(alpha) * t  (from C(t)^2 >= alpha * t^2).
    Upper bound: C(t) <= (C(1) + 2t/sqrt(alpha)) (from increment <= 2/sqrt(alpha)). -/
theorem cumulative_attention_growth
    (C : ℕ → ℝ) (a : ℕ → ℝ)
    (α : ℝ) (hα : 0 < α)
    (ha_lower : ∀ t, α ≤ a t)
    (ha_upper : ∀ t, a t ≤ 1)
    (hC_pos : 0 < C 0)
    -- C evolves by the accumulation rule (LINEAR form, not squared)
    (h_step : ∀ t, C (t + 1) = C t + a t * (↑t + 1) / C t) :
    -- C(t) > 0 for all t, and C(t) = Theta(t)
    (∀ t, 0 < C t) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ t, 1 ≤ t →
      c₁ * ↑t ≤ C t ∧ C t ≤ c₂ * ↑t := by
  -- Step 1: C(t) > 0 for all t by induction (linear step preserves positivity).
  have hC_pos_all : ∀ t, 0 < C t := by
    intro t
    induction t with
    | zero => exact hC_pos
    | succ t ih =>
      have ha_t : 0 < a t := lt_of_lt_of_le hα (ha_lower t)
      rw [h_step t]
      have h1 : 0 < a t * ((↑t : ℝ) + 1) / C t := by positivity
      linarith
  constructor
  · exact hC_pos_all
  -- Step 2: C(t)^2 grows at least quadratically: C(t)^2 >= alpha * t^2.
  have hC_sq_lower : ∀ t : ℕ, α * (t : ℝ) ^ 2 ≤ C t ^ 2 := by
    intro t
    induction t with
    | zero => simp [sq_nonneg]
    | succ t ih =>
      have hCt_pos : 0 < C t := hC_pos_all t
      have ha_lo : α ≤ a t := ha_lower t
      -- C(t+1)^2 = (C(t) + a(t)*(t+1)/C(t))^2
      --          = C(t)^2 + 2*a(t)*(t+1) + (a(t)*(t+1)/C(t))^2
      have h_sq : C (t + 1) ^ 2 = C t ^ 2 + 2 * a t * ((↑t : ℝ) + 1) +
          (a t * ((↑t : ℝ) + 1) / C t) ^ 2 := by
        rw [h_step t]; field_simp; ring
      have h2 : 0 ≤ (a t * ((↑t : ℝ) + 1) / C t) ^ 2 := sq_nonneg _
      have hmono : 2 * α * ((t : ℝ) + 1) ≤ 2 * a t * ((t : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have hcast : α * ((↑(t + 1) : ℝ)) ^ 2 = α * (↑t : ℝ) ^ 2 + α * (2 * (↑t : ℝ) + 1) := by
        push_cast; ring
      have hα_le : α * (2 * (↑t : ℝ) + 1) ≤ 2 * α * ((t : ℝ) + 1) := by nlinarith
      push_cast at h_sq ⊢
      nlinarith
  -- Step 3: Lower bound C(t) >= sqrt(alpha) * t for t >= 1.
  have hC_lower : ∀ t : ℕ, 1 ≤ t → Real.sqrt α * (t : ℝ) ≤ C t := by
    intro t ht
    have hCt_pos : 0 < C t := hC_pos_all t
    have hC_sq : α * (t : ℝ) ^ 2 ≤ C t ^ 2 := hC_sq_lower t
    have h_lhs : (0 : ℝ) ≤ Real.sqrt α * (t : ℝ) := by positivity
    have h_sq_eq : (Real.sqrt α * (t : ℝ)) ^ 2 = α * (t : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hα)]
    nlinarith [sq_nonneg (C t - Real.sqrt α * (t : ℝ)), sq_abs (C t)]
  -- Step 4: Bound on increment: C(t+1) - C(t) <= 2/sqrt(alpha) for t >= 1.
  have hsqrt_pos : (0 : ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hC_incr_bound : ∀ t : ℕ, 1 ≤ t →
      C (t + 1) - C t ≤ 2 / Real.sqrt α := by
    intro t ht
    have hCt_pos : 0 < C t := hC_pos_all t
    have hCt_lower : Real.sqrt α * (↑t : ℝ) ≤ C t := hC_lower t ht
    have hincr : C (t + 1) - C t = a t * ((↑t : ℝ) + 1) / C t := by linarith [h_step t]
    have ha_t : a t ≤ 1 := ha_upper t
    have h1 : a t * ((↑t : ℝ) + 1) / C t ≤ ((↑t : ℝ) + 1) / C t := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hCt_pos)
      nlinarith [ha_lower t]
    have ht_real_pos : (0 : ℝ) < (↑t : ℝ) := by exact_mod_cast ht
    have h2 : ((↑t : ℝ) + 1) / C t ≤ ((↑t : ℝ) + 1) / (Real.sqrt α * (↑t : ℝ)) := by
      apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (↑t : ℝ) + 1)
        (by positivity : 0 < Real.sqrt α * (↑t : ℝ)) hCt_lower
    have h3 : ((↑t : ℝ) + 1) / (Real.sqrt α * (↑t : ℝ)) ≤ 2 / Real.sqrt α := by
      have h_denom_pos : (0 : ℝ) < Real.sqrt α * (↑t : ℝ) := by positivity
      rw [div_le_div_iff₀ h_denom_pos hsqrt_pos]
      have ht_ge : (1 : ℝ) ≤ (↑t : ℝ) := by exact_mod_cast ht
      have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt α := le_of_lt hsqrt_pos
      nlinarith [le_mul_of_one_le_right hsqrt_nn ht_ge]
    linarith
  -- Step 5: Upper bound C(t) <= C(1) + t * (2/sqrt(alpha)) for t >= 1 (via induction).
  have hC_lin_upper : ∀ t : ℕ, 1 ≤ t → C t ≤ C 1 + (↑t : ℝ) * (2 / Real.sqrt α) := by
    intro t ht
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht0 : t = 0
      · subst ht0; simp; linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hsqrt_pos)]
      · have ht_ge : 1 ≤ t := by omega
        have ih_t := ih ht_ge
        have hincr := hC_incr_bound t ht_ge
        have hstep_ub : C (t + 1) ≤ C t + 2 / Real.sqrt α := by linarith
        have hcast : (↑(t + 1) : ℝ) * (2 / Real.sqrt α) =
            (↑t : ℝ) * (2 / Real.sqrt α) + 2 / Real.sqrt α := by push_cast; ring
        linarith
  -- C(t) <= C(1) + t * 2/sqrt(alpha) <= (C(1) + 2/sqrt(alpha)) * t for t >= 1
  have hC_upper : ∀ t : ℕ, 1 ≤ t → C t ≤ (C 1 + 2 / Real.sqrt α) * (↑t : ℝ) := by
    intro t ht
    have h := hC_lin_upper t ht
    have ht_ge : (1 : ℝ) ≤ (↑t : ℝ) := by exact_mod_cast ht
    have hC1_pos' : 0 < C 1 := hC_pos_all 1
    nlinarith
  have hC1_pos : 0 < C 1 := hC_pos_all 1
  exact ⟨Real.sqrt α, C 1 + 2 / Real.sqrt α, Real.sqrt_pos.mpr hα,
    by positivity, fun t ht => ⟨hC_lower t ht, hC_upper t ht⟩⟩

/-- Paper: lem:sigma_increment (main).
    |sigma_{t+1}(tau) - sigma_t(tau)| = O(1/t).
    Proof: sigma_t = C_t / N_t with N_t = N_0 + t.
    The numerator of sigma_{t+1} - sigma_t is
      C_{t+1}*(N_0+t) - C_t*(N_0+t+1) = a_t*(t+1)*(N_0+t)/C_t - C_t.
    The denominator is (N_0+t)*(N_0+t+1).
    We bound |numerator| <= K*t and denominator >= t^2, giving O(1/t). -/
theorem sigma_increment_bound
    (C : ℕ → ℝ) (N₀ : ℕ) (hN₀ : 0 < N₀)
    -- C evolves by accumulation
    (a : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (ha_lower : ∀ t, α ≤ a t)
    (ha_upper : ∀ t, a t ≤ 1)
    (hC_pos : 0 < C 0)
    (h_step : ∀ t, C (t + 1) = C t + a t * (↑t + 1) / C t) :
    -- There exists a constant K (depending on α, N₀) such that
    -- |σ_{t+1} - σ_t| ≤ K / t for t ≥ 1
    ∃ K_const : ℝ, 0 < K_const ∧ ∀ t : ℕ, 1 ≤ t →
      |C (t + 1) / (↑(N₀ + t + 1) : ℝ) - C t / (↑(N₀ + t) : ℝ)|
        ≤ K_const / ↑t := by
  -- Step 1: C(t) > 0 for all t by induction using the linear step.
  have hC_pos_all : ∀ t, 0 < C t := by
    intro t
    induction t with
    | zero => exact hC_pos
    | succ t ih =>
      have ha_t : 0 < a t := lt_of_lt_of_le hα (ha_lower t)
      rw [h_step t]
      have h1 : 0 < a t * ((↑t : ℝ) + 1) / C t := by positivity
      linarith
  -- Step 2: C is monotone (C(0) ≤ C(t) for all t).
  have hC_ge_init : ∀ t, C 0 ≤ C t := by
    intro t
    induction t with
    | zero => exact le_refl _
    | succ t ih =>
      have ha_t : 0 < a t := lt_of_lt_of_le hα (ha_lower t)
      have hCt_pos : 0 < C t := hC_pos_all t
      have h_step_t : C (t + 1) = C t + a t * ((↑t : ℝ) + 1) / C t := h_step t
      have h_incr : 0 < a t * ((↑t : ℝ) + 1) / C t := by positivity
      linarith
  -- Step 3: C(t)² grows at least quadratically: C(t)² ≥ α · t².
  have hC_sq_lower : ∀ t : ℕ, α * (t : ℝ) ^ 2 ≤ C t ^ 2 := by
    intro t
    induction t with
    | zero => simp [sq_nonneg]
    | succ t ih =>
      have hCt_pos : 0 < C t := hC_pos_all t
      have ha_lo : α ≤ a t := ha_lower t
      have h_at_pos : 0 < a t := lt_of_lt_of_le hα ha_lo
      -- C(t+1)² = (C(t) + a(t)·(t+1)/C(t))² = C(t)² + 2·a(t)·(t+1) + a(t)²·(t+1)²/C(t)²
      have h_sq : C (t + 1) ^ 2 = C t ^ 2 + 2 * a t * ((↑t : ℝ) + 1) +
          (a t * ((↑t : ℝ) + 1) / C t) ^ 2 := by
        have hstep := h_step t
        have hCt_ne : C t ≠ 0 := ne_of_gt hCt_pos
        rw [hstep]; field_simp; ring
      have h2 : 0 ≤ (a t * ((↑t : ℝ) + 1) / C t) ^ 2 := sq_nonneg _
      have hmono : 2 * α * ((t : ℝ) + 1) ≤ 2 * a t * ((t : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have hcast : α * ((↑(t + 1) : ℝ)) ^ 2 = α * (↑t : ℝ) ^ 2 + α * (2 * (↑t : ℝ) + 1) := by
        push_cast; ring
      have hα_le : α * (2 * (↑t : ℝ) + 1) ≤ 2 * α * ((t : ℝ) + 1) := by nlinarith
      push_cast at h_sq ⊢
      nlinarith
  -- Step 4: Lower bound C(t) ≥ √α · t for t ≥ 1.
  have hC_lower : ∀ t : ℕ, 1 ≤ t → Real.sqrt α * (t : ℝ) ≤ C t := by
    intro t ht
    have hCt_pos : 0 < C t := hC_pos_all t
    have hC_sq : α * (t : ℝ) ^ 2 ≤ C t ^ 2 := hC_sq_lower t
    have h_lhs : (0 : ℝ) ≤ Real.sqrt α * (t : ℝ) := by positivity
    have h_sq_eq : (Real.sqrt α * (t : ℝ)) ^ 2 = α * (t : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hα)]
    nlinarith [sq_nonneg (C t - Real.sqrt α * (t : ℝ)), sq_abs (C t)]
  -- Step 5: Upper bound on C(t)² via telescoping.
  -- C(t+1)² = C(t)² + 2·a(t)·(t+1) + (a(t)·(t+1)/C(t))²
  -- ≤ C(t)² + 2·(t+1) + (t+1)²/C(t)² (using a(t) ≤ 1)
  -- ≤ C(t)² + 2·(t+1) + (t+1)²/(α·t²) (using C(t)² ≥ α·t² for t ≥ 1)
  -- For t ≥ 1: (t+1)²/(α·t²) ≤ 4/α.
  -- Telescoping from 1: C(t)² ≤ C(1)² + Σ_{s=1}^{t-1} (2·(s+1) + 4/α)
  -- ≤ C(1)² + t² + t + 4t/α ≤ M² · t² for some M.
  -- Rather than formalize the full telescoping, we use a direct bound:
  -- C(t+1) = C(t) + a(t)·(t+1)/C(t) ≤ C(t) + (t+1)/C(t) ≤ C(t) + (t+1)/(√α·t)
  -- For t ≥ 1: (t+1)/t ≤ 2, so increment ≤ 2/√α.
  -- So C(t) ≤ C(1) + 2·(t-1)/√α.
  have hC_incr_bound : ∀ t : ℕ, 1 ≤ t →
      C (t + 1) - C t ≤ 2 / Real.sqrt α := by
    intro t ht
    have hCt_pos : 0 < C t := hC_pos_all t
    have hCt_lower : Real.sqrt α * (↑t : ℝ) ≤ C t := hC_lower t ht
    have hsqrt_pos : (0 : ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
    have h_step_t := h_step t
    -- C(t+1) - C(t) = a(t)·(t+1)/C(t) ≤ 1·(t+1)/C(t) ≤ (t+1)/(√α·t)
    have hincr : C (t + 1) - C t = a t * ((↑t : ℝ) + 1) / C t := by linarith
    -- a(t) ≤ 1
    have ha_t : a t ≤ 1 := ha_upper t
    -- a(t)·(t+1)/C(t) ≤ (t+1)/C(t)
    have h1 : a t * ((↑t : ℝ) + 1) / C t ≤ ((↑t : ℝ) + 1) / C t := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hCt_pos)
      nlinarith [ha_lower t]
    -- (t+1)/C(t) ≤ (t+1)/(√α·t) since C(t) ≥ √α·t
    have ht_real_pos : (0 : ℝ) < (↑t : ℝ) := by exact_mod_cast ht
    have h2 : ((↑t : ℝ) + 1) / C t ≤ ((↑t : ℝ) + 1) / (Real.sqrt α * (↑t : ℝ)) := by
      apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (↑t : ℝ) + 1)
        (by positivity : 0 < Real.sqrt α * (↑t : ℝ)) hCt_lower
    -- (t+1)/(√α·t) = (1/√α)·(t+1)/t ≤ (1/√α)·2 = 2/√α for t ≥ 1
    have h3 : ((↑t : ℝ) + 1) / (Real.sqrt α * (↑t : ℝ)) ≤ 2 / Real.sqrt α := by
      -- (t+1)/(√α·t) ≤ 2/√α ⟺ (t+1)·√α ≤ 2·(√α·t) (clearing positive denominators)
      -- ⟺ √α·(t+1) ≤ 2·√α·t ⟺ t+1 ≤ 2·t (since √α > 0) ⟺ 1 ≤ t. True by ht.
      have h_denom_pos : (0 : ℝ) < Real.sqrt α * (↑t : ℝ) := by positivity
      rw [div_le_div_iff₀ h_denom_pos hsqrt_pos]
      -- Goal: (↑t + 1) * √α ≤ 2 * (√α * ↑t)
      -- Equivalently: √α ≤ √α * ↑t, since 1 ≤ ↑t
      have ht_ge : (1 : ℝ) ≤ (↑t : ℝ) := by exact_mod_cast ht
      have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt α := le_of_lt hsqrt_pos
      have key : Real.sqrt α ≤ Real.sqrt α * (↑t : ℝ) :=
        le_mul_of_one_le_right hsqrt_nn ht_ge
      nlinarith
    linarith
  -- Step 6: Upper bound C(t) ≤ (C(1) + 2/√α) · t for t ≥ 1.
  -- We use C(t) ≤ C(1) + Σ_{s=1}^{t-1} 2/√α ≤ C(1) + 2·t/√α for t ≥ 1.
  -- Actually, a simpler approach: C(t) ≤ C(0) + t · (max increment over [0..t-1]).
  -- For t = 0: trivial (no constraint needed).
  -- For the bound, note C(t) = C(0) + Σ_{s=0}^{t-1} Δ(s) where Δ(0) might be large.
  -- Simpler: C(t) ≤ C(1) · t for t ≥ 1 IF C is subadditive... actually not obvious.
  -- Use: C(t) ≤ C(0) + (C(1) - C(0)) + Σ_{s=1}^{t-1} 2/√α ≤ C(1) + 2·t/√α.
  -- Therefore C(t)/t ≤ C(1)/t + 2/√α ≤ C(1) + 2/√α for t ≥ 1.
  -- We choose K = C(1) + 2/√α + 2/√α (combining both terms).
  --
  -- Full algebraic derivation:
  -- |σ(t+1) - σ(t)| = |(-C(t) + a(t)·(t+1)·(N₀+t)/C(t)) / ((N₀+t)·(N₀+t+1))|
  -- ≤ (C(t) + (t+1)·(N₀+t)/C(t)) / ((N₀+t)·(N₀+t+1))
  -- = C(t)/((N₀+t)·(N₀+t+1)) + (t+1)/(C(t)·(N₀+t+1))
  -- ≤ C(t)/t² + 2/(√α·t)    (using N₀+t ≥ t, C(t) ≥ √α·t, (t+1)/(N₀+t+1) ≤ 1)
  -- and C(t)/t ≤ some constant M, so overall ≤ (M + 2/√α)/t.
  --
  -- The K constant depends on C(0), α, and N₀.
  use C 1 + 2 / Real.sqrt α + 2 / Real.sqrt α
  constructor
  · -- K > 0
    have : 0 < C 1 := hC_pos_all 1
    have : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
    positivity
  · -- The bound
    intro t ht
    have hsqrt_pos : (0 : ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
    have hCt_pos : 0 < C t := hC_pos_all t
    have ht_real_pos : (0 : ℝ) < (↑t : ℝ) := by exact_mod_cast ht
    have hNt_pos : (0 : ℝ) < (↑(N₀ + t) : ℝ) := by positivity
    have hNt1_pos : (0 : ℝ) < (↑(N₀ + t + 1) : ℝ) := by positivity
    -- (A) Upper bound on C(t) for t ≥ 1 via telescoping increments.
    have hC_upper : ∀ s : ℕ, 1 ≤ s → C s ≤ C 1 + (↑s : ℝ) * (2 / Real.sqrt α) := by
      intro s hs
      induction s with
      | zero => omega
      | succ s ih =>
        by_cases hs1 : s = 0
        · subst hs1
          simp
          have : 0 ≤ 2 / Real.sqrt α := by positivity
          linarith
        · have hs_ge : 1 ≤ s := by omega
          have ih_s := ih hs_ge
          have hincr := hC_incr_bound s hs_ge
          have hstep_s : C (s + 1) ≤ C s + 2 / Real.sqrt α := by linarith
          have hcast : (↑(s + 1) : ℝ) * (2 / Real.sqrt α) =
              (↑s : ℝ) * (2 / Real.sqrt α) + 2 / Real.sqrt α := by push_cast; ring
          linarith
    -- (B) C(t)/t is bounded by a constant
    have hC_over_t : C t / (↑t : ℝ) ≤ C 1 + 2 / Real.sqrt α := by
      have hCt_upper := hC_upper t ht
      rw [div_le_iff₀ ht_real_pos]
      have hC1_pos : 0 < C 1 := hC_pos_all 1
      have ht_ge : (1 : ℝ) ≤ (↑t : ℝ) := by exact_mod_cast ht
      nlinarith [mul_le_mul_of_nonneg_right ht_ge (le_of_lt hC1_pos)]
    -- (C) Decompose the sigma increment.
    set Δ := a t * ((↑t : ℝ) + 1) / C t with hΔ_def
    have hΔ_pos : 0 ≤ Δ := by
      change 0 ≤ a t * ((↑t : ℝ) + 1) / C t
      apply div_nonneg (mul_nonneg (by linarith [ha_lower t]) (by positivity)) (le_of_lt hCt_pos)
    have hstep_t : C (t + 1) = C t + Δ := h_step t
    have h_diff : C (t + 1) / (↑(N₀ + t + 1) : ℝ) - C t / (↑(N₀ + t) : ℝ) =
        Δ / (↑(N₀ + t + 1) : ℝ) - C t / ((↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ)) := by
      rw [hstep_t]
      have hne1 : (↑(N₀ + t) : ℝ) ≠ 0 := ne_of_gt hNt_pos
      have hne2 : (↑(N₀ + t + 1) : ℝ) ≠ 0 := ne_of_gt hNt1_pos
      -- (C(t) + Δ) / (N₀+t+1) - C(t) / (N₀+t)
      -- = C(t)/(N₀+t+1) + Δ/(N₀+t+1) - C(t)/(N₀+t)
      -- = Δ/(N₀+t+1) - C(t) · (1/(N₀+t) - 1/(N₀+t+1))
      -- = Δ/(N₀+t+1) - C(t) / ((N₀+t)·(N₀+t+1))
      field_simp; push_cast; ring
    -- (D) |diff| ≤ Δ/(N₀+t+1) + C(t)/((N₀+t)·(N₀+t+1))
    have h1_nn : 0 ≤ Δ / (↑(N₀ + t + 1) : ℝ) := by positivity
    have h2_nn : 0 ≤ C t / ((↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ)) := by positivity
    have h_abs_bound : |C (t + 1) / (↑(N₀ + t + 1) : ℝ) - C t / (↑(N₀ + t) : ℝ)| ≤
        Δ / (↑(N₀ + t + 1) : ℝ) + C t / ((↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ)) := by
      rw [h_diff]
      -- |a - b| ≤ a + b (since a, b ≥ 0), using abs_le
      rw [abs_le]
      constructor
      · linarith
      · linarith
    -- (E) Bound Δ/(N₀+t+1) ≤ (2/√α)/t
    have hΔ_bound : Δ ≤ 2 / Real.sqrt α := by linarith [hC_incr_bound t ht]
    have hNt1_ge_t : (↑t : ℝ) ≤ (↑(N₀ + t + 1) : ℝ) := by
      push_cast; linarith [show (0 : ℝ) < ↑N₀ from by exact_mod_cast hN₀]
    have h_term1 : Δ / (↑(N₀ + t + 1) : ℝ) ≤ (2 / Real.sqrt α) / (↑t : ℝ) := by
      calc Δ / (↑(N₀ + t + 1) : ℝ)
          ≤ (2 / Real.sqrt α) / (↑(N₀ + t + 1) : ℝ) :=
            div_le_div_of_nonneg_right hΔ_bound (by positivity)
        _ ≤ (2 / Real.sqrt α) / (↑t : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) ht_real_pos hNt1_ge_t
    -- (F) Bound C(t)/((N₀+t)·(N₀+t+1)) ≤ (C(1)+2/√α)/t
    have hNt_ge_t : (↑t : ℝ) ≤ (↑(N₀ + t) : ℝ) := by
      push_cast; linarith [show (0 : ℝ) ≤ ↑N₀ from by exact_mod_cast (Nat.zero_le N₀)]
    have h_denom_bound : (↑t : ℝ) * (↑t : ℝ) ≤
        (↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ) :=
      mul_le_mul hNt_ge_t hNt1_ge_t (le_of_lt ht_real_pos) (by positivity)
    have h_term2 : C t / ((↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ)) ≤
        (C 1 + 2 / Real.sqrt α) / (↑t : ℝ) := by
      have h_frac : C t / ((↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ)) ≤
          C t / ((↑t : ℝ) * (↑t : ℝ)) :=
        div_le_div_of_nonneg_left (le_of_lt hCt_pos)
          (by positivity) h_denom_bound
      have h_rewrite : C t / ((↑t : ℝ) * (↑t : ℝ)) = (C t / (↑t : ℝ)) / (↑t : ℝ) := by
        rw [div_div]
      calc C t / ((↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ))
          ≤ (C t / (↑t : ℝ)) / (↑t : ℝ) := by linarith [h_frac, h_rewrite.symm]
        _ ≤ (C 1 + 2 / Real.sqrt α) / (↑t : ℝ) :=
            div_le_div_of_nonneg_right hC_over_t (le_of_lt ht_real_pos)
    -- (G) Combine
    calc |C (t + 1) / (↑(N₀ + t + 1) : ℝ) - C t / (↑(N₀ + t) : ℝ)|
        ≤ Δ / (↑(N₀ + t + 1) : ℝ) +
          C t / ((↑(N₀ + t) : ℝ) * (↑(N₀ + t + 1) : ℝ)) := h_abs_bound
      _ ≤ (2 / Real.sqrt α) / (↑t : ℝ) + (C 1 + 2 / Real.sqrt α) / (↑t : ℝ) := by
          linarith [h_term1, h_term2]
      _ = (C 1 + 2 / Real.sqrt α + 2 / Real.sqrt α) / (↑t : ℝ) := by ring

/-- Paper: lem:sigma_increment (corollary -- sigma converges).
    sigma_t converges when it is eventually monotone and bounded.

    The paper's argument (thm:selective part (iii)) shows sigma is
    self-regulating: when sigma > K for large enough K, the increment is negative,
    so sigma is eventually non-increasing (or non-decreasing from below). This
    eventual monotonicity, combined with boundedness, gives convergence by the
    monotone convergence theorem.

    NOTE: O(1/t) increments alone do NOT imply convergence (the harmonic series
    diverges, and sequences like sin(log(t)) have O(1/t) increments but don't
    converge). The fix adds eventual monotonicity, which is what the paper
    actually derives from the self-regulation argument. -/
theorem sigma_converges
    (σ : ℕ → ℝ)
    -- σ is bounded
    (h_bdd : ∃ B : ℝ, ∀ t, |σ t| ≤ B)
    -- σ is eventually monotone (the key structural property from the paper)
    (h_evt_mono : ∃ T : ℕ, ∀ t, T ≤ t → σ t ≤ σ (t + 1)) :
    ∃ σ_star : ℝ, Filter.Tendsto σ Filter.atTop (nhds σ_star) := by
  obtain ⟨B, hB⟩ := h_bdd
  obtain ⟨T, hT⟩ := h_evt_mono
  -- Define the shifted sequence g(n) = σ(T + n), which is monotone and bounded.
  set g := fun n => σ (T + n) with hg_def
  -- g is monotone
  have hg_mono : Monotone g := by
    intro a b hab
    simp only [hg_def]
    -- Prove by obtaining b = a + k and inducting on k
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : σ (T + a) ≤ σ (T + (a + k)) := ih (Nat.le_add_right a k)
      have h2 : σ (T + (a + k)) ≤ σ (T + (a + k) + 1) := hT (T + (a + k)) (by omega)
      have h3 : T + (a + k) + 1 = T + (a + (k + 1)) := by omega
      rw [h3] at h2
      exact le_trans h1 h2
  -- g is bounded above
  have hg_bdd : BddAbove (Set.range g) := by
    use B
    intro x ⟨n, hn⟩
    rw [← hn]
    exact le_of_abs_le (hB (T + n))
  -- g converges by the monotone convergence theorem
  have hg_conv : Tendsto g atTop (nhds (⨆ n, g n)) :=
    tendsto_atTop_ciSup hg_mono hg_bdd
  -- σ converges to the same limit (since g is a tail of σ)
  use ⨆ n, g n
  -- σ(t) = g(t - T) for t ≥ T, so σ converges to the same limit as g.
  rw [Metric.tendsto_atTop] at hg_conv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hg_conv ε hε
  use T + N
  intro t ht
  have hk_eq : T + (t - T) = t := by omega
  specialize hN (t - T) (by omega)
  simp only [hg_def, hk_eq] at hN
  exact hN
