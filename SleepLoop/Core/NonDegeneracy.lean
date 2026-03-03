/-
  SleepLoop/Core/NonDegeneracy.lean

  Theorem 8 (thm:nondegen): Non-degeneracy of attention.
  Under bounded |S(tau)| <= B_S, there exists alpha > 0 such that
  a_t(tau) >= alpha for all tau in X and all t >= 0.
  Level: 𝒜₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Observation
import SleepLoop.Core.SelectivePersistence
import SleepLoop.Core.BoundedBias
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Basic

open Finset BigOperators

/-! ## Non-Degeneracy -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d n : ℕ}

/-- thm:nondegen: Under A+ with bounded |S(τ)| ≤ B_S,
    there exists α > 0 such that a_t(τ) ≥ α for all τ, t.
    The bound depends on φ, B_S, C₀, |X|, R, ‖K‖_op. -/
theorem nondegeneracy
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (B_S : ℝ) (σ_max : ℝ) (b_max : ℝ)
    (_hB_S : 0 ≤ B_S) (_hσ : 0 ≤ σ_max) (_hb : 0 ≤ b_max) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (S σ b : Fin n → ℝ),
        (∀ i, |S i| ≤ B_S) →
        (∀ i, |σ i| ≤ σ_max) →
        (∀ i, |b i| ≤ b_max) →
        ∀ i, α ≤ φ (fun j => S j + σ j + b j) i := by
  -- n = 0: Fin 0 is empty, conclusion is vacuous for any α > 0.
  by_cases hn : n = 0
  · subst hn
    exact ⟨1, one_pos, fun _ _ _ _ _ _ i => Fin.elim0 i⟩
  -- n ≥ 1: Use continuity of φ (from PositiveSimplexMap.cont) + compactness.
  -- The set of all inputs x = S + σ + b with |S i| ≤ B_S, |σ i| ≤ σ_max, |b i| ≤ b_max
  -- satisfies |x i| ≤ B where B = B_S + σ_max + b_max, so x lies in the compact box
  -- {x : Fin n → ℝ | ∀ i, x i ∈ [-B, B]}.
  -- For each i, the map x ↦ φ x i is continuous and strictly positive on this compact set,
  -- so it attains a positive minimum α_i > 0. Take α = min_i α_i > 0.
  haveI : NeZero n := ⟨hn⟩
  set B := B_S + σ_max + b_max with B_def
  -- The compact box
  set box := Set.pi Set.univ (fun (_ : Fin n) => Set.Icc (-B) B) with box_def
  -- The box is compact (product of compact intervals)
  have hbox_compact : IsCompact box :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  -- The box is nonempty (0 is in it since B ≥ 0)
  have hB_nn : 0 ≤ B := by linarith
  have hbox_nonempty : box.Nonempty :=
    ⟨0, fun i _ => by simp only [Pi.zero_apply, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩⟩
  -- Each component φ(·) i is continuous
  have hφ_cont : Continuous φ := PositiveSimplexMap.cont
  -- For each i, the function x ↦ φ x i is continuous
  have hφi_cont : ∀ i : Fin n, Continuous (fun x => φ x i) := by
    intro i; exact (continuous_apply i).comp hφ_cont
  -- For each i, φ x i > 0 on the box
  have hφi_pos : ∀ (x : Fin n → ℝ) (i : Fin n), 0 < φ x i :=
    fun x i => PositiveSimplexMap.pos x i
  -- For each i, find the minimum of φ(·) i on the compact box.
  -- On a compact nonempty set, a continuous function attains its infimum.
  have hφi_min : ∀ i : Fin n, ∃ x₀ ∈ box, ∀ x ∈ box, φ x₀ i ≤ φ x i := by
    intro i
    exact hbox_compact.exists_isMinOn hbox_nonempty (hφi_cont i).continuousOn
  -- Collect the minima: for each i, get α_i = φ(x₀_i) i > 0
  -- Then take α = min over all i of α_i > 0.
  -- Since Fin n is finite and nonempty, we can take the min.
  -- Simple approach: use Finset.inf' over the minimum values.
  choose x₀ hx₀_mem hx₀_min using hφi_min
  set αs := fun i => φ (x₀ i) i with αs_def
  have hαs_pos : ∀ i, 0 < αs i := fun i => hφi_pos (x₀ i) i
  -- Take α = inf of αs over Fin n
  haveI : Nonempty (Fin n) := inferInstance
  set α := Finset.inf' Finset.univ Finset.univ_nonempty αs with α_def
  refine ⟨α, ?_, ?_⟩
  · -- α > 0: inf of positive values over nonempty finite set is positive
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty αs
    rw [α_def, hj]; exact hαs_pos j
  · -- The bound: for any bounded S, σ, b and any i, α ≤ φ(S+σ+b) i
    intro S σ b hS hσ hb i
    -- First show the input x = fun j => S j + σ j + b j is in the box
    have hx_in_box : (fun j => S j + σ j + b j) ∈ box := by
      intro j _
      simp only [Set.mem_Icc]
      constructor
      · have := abs_le.mp (show |S j| ≤ B_S from hS j)
        have := abs_le.mp (show |σ j| ≤ σ_max from hσ j)
        have := abs_le.mp (show |b j| ≤ b_max from hb j)
        linarith
      · have := abs_le.mp (show |S j| ≤ B_S from hS j)
        have := abs_le.mp (show |σ j| ≤ σ_max from hσ j)
        have := abs_le.mp (show |b j| ≤ b_max from hb j)
        linarith
    -- α ≤ αs i ≤ φ(x₀ i) i ≤ φ(S+σ+b) i
    calc α ≤ αs i :=
          Finset.inf'_le _ (Finset.mem_univ i)
      _ ≤ φ (fun j => S j + σ j + b j) i :=
          hx₀_min i (fun j => S j + σ j + b j) hx_in_box

/-- thm:nondegen (softmax explicit bound): Under softmax,
    α = exp(-2B) / n where B = B_S + σ_max + R² ‖K‖_op. -/
theorem nondegeneracy_softmax
    (n : ℕ) [NeZero n]
    (B : ℝ) (_hB : 0 ≤ B)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ B) (i : Fin n) :
    Real.exp (-2 * B) / n ≤ softmax x i := by
  unfold softmax
  -- Goal: exp(-2B)/n ≤ exp(x i) / ∑ j, exp(x j)
  have h_denom_pos : 0 < ∑ j : Fin n, Real.exp (x j) := softmax_denom_pos x
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (NeZero.pos n)
  -- Step 1: Lower bound on numerator: exp(x i) ≥ exp(-B)
  have hxi_lower : -B ≤ x i := by
    have := hx i; rw [abs_le] at this; exact this.1
  have h_num_lower : Real.exp (-B) ≤ Real.exp (x i) :=
    Real.exp_le_exp.mpr hxi_lower
  -- Step 2: Upper bound on denominator: ∑ j, exp(x j) ≤ n * exp(B)
  have h_exp_upper : ∀ j, Real.exp (x j) ≤ Real.exp B := by
    intro j; apply Real.exp_le_exp.mpr
    have := hx j; rw [abs_le] at this; exact this.2
  have h_denom_upper : ∑ j : Fin n, Real.exp (x j) ≤ ↑n * Real.exp B := by
    calc ∑ j : Fin n, Real.exp (x j)
        ≤ ∑ _j : Fin n, Real.exp B :=
          Finset.sum_le_sum (fun j _ => h_exp_upper j)
      _ = ↑n * Real.exp B := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Step 3: Use cross-multiplication to prove the inequality
  -- exp(-2B)/n ≤ exp(x i) / sum  ↔  exp(-2B) * sum ≤ exp(x i) * n
  rw [div_le_div_iff₀ hn_pos h_denom_pos]
  -- Goal: exp(-2B) * ∑ j, exp(x j) ≤ exp(x i) * ↑n
  -- Chain: exp(-2B) * sum ≤ exp(-2B) * (n * exp B) = n * exp(-2B) * exp(B)
  --        = n * exp(-B) ≤ n * exp(x i) = exp(x i) * n
  have h1 : Real.exp (-2 * B) * ∑ j : Fin n, Real.exp (x j) ≤
      Real.exp (-2 * B) * (↑n * Real.exp B) :=
    mul_le_mul_of_nonneg_left h_denom_upper (le_of_lt (Real.exp_pos _))
  have h2 : Real.exp (-2 * B) * (↑n * Real.exp B) = ↑n * Real.exp (-B) := by
    rw [show (-2 : ℝ) * B = -B + (-B) from by ring, Real.exp_add]
    have hcancel : Real.exp (-B) * Real.exp B = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-B) * Real.exp (-B) * (↑n * Real.exp B)
        = ↑n * (Real.exp (-B) * (Real.exp (-B) * Real.exp B)) := by ring
      _ = ↑n * (Real.exp (-B) * 1) := by rw [hcancel]
      _ = ↑n * Real.exp (-B) := by ring
  have h3 : ↑n * Real.exp (-B) ≤ ↑n * Real.exp (x i) :=
    mul_le_mul_of_nonneg_left h_num_lower (le_of_lt hn_pos)
  linarith
