/-
  SleepLoop/Defs/SimplexMap.lean

  Definition: The three-level simplex map hierarchy A > A_+ > {softmax}.
  Formalizes SimplexMap (A), PositiveSimplexMap (A_+), and softmax.
  Paper: §2.1 (setup paragraph), §2.2 (Proposition 7, Table 1).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.Basic

open Finset BigOperators

/-! ## Simplex Map Hierarchy -/

/-- A simplex map sends ℝⁿ to the probability simplex Δⁿ.
    This is the broadest level (A) in the paper's hierarchy.
    Paper: §2.1 (setup paragraph). -/
class SimplexMap {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ)) : Prop where
  nonneg : ∀ x i, 0 ≤ φ x i
  sum_one : ∀ x, ∑ i : Fin n, φ x i = 1

/-- A positive order-preserving simplex map (A_+ level).
    All outputs strictly positive, ordering preserved, and continuous.
    Paper: §2.1 (setup paragraph). -/
class PositiveSimplexMap {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ))
    : Prop extends SimplexMap φ where
  pos : ∀ x i, 0 < φ x i
  order_preserving : ∀ x (i j : Fin n), x i > x j → φ x i > φ x j
  cont : Continuous φ

/-! ## Softmax -/

/-- The softmax map: φ(x)ᵢ = exp(xᵢ) / Σⱼ exp(xⱼ).
    Paper: §2.1 (setup paragraph). -/
noncomputable def softmax {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (x i) / ∑ j : Fin n, Real.exp (x j)

/-- Softmax with inverse temperature β. -/
noncomputable def softmaxBeta {n : ℕ} (β : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (β * x i) / ∑ j : Fin n, Real.exp (β * x j)

/-- The softmax denominator is always positive (for n ≥ 1). -/
theorem softmax_denom_pos {n : ℕ} [hn : NeZero n] (x : Fin n → ℝ) :
    0 < ∑ j : Fin n, Real.exp (x j) := by
  apply Finset.sum_pos
  · intro j _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Softmax is a PositiveSimplexMap (for n ≥ 1).
    Paper: §2.1 ("Softmax is positive"). -/
instance softmax_positiveSimplexMap {n : ℕ} [NeZero n] :
    PositiveSimplexMap (softmax : (Fin n → ℝ) → (Fin n → ℝ)) where
  nonneg := fun x i => by
    unfold softmax
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (softmax_denom_pos x))
  sum_one := fun x => by
    unfold softmax
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (softmax_denom_pos x))
  pos := fun x i => by
    unfold softmax
    exact div_pos (Real.exp_pos _) (softmax_denom_pos x)
  order_preserving := fun x i j hij => by
    unfold softmax
    exact div_lt_div_of_pos_right (Real.exp_strictMono hij) (softmax_denom_pos x)
  cont := by
    apply continuous_pi; intro i
    change Continuous (fun (y : Fin n → ℝ) => Real.exp (y i) / ∑ j : Fin n, Real.exp (y j))
    apply Continuous.div
    · exact Real.continuous_exp.comp (continuous_apply i)
    · exact continuous_finset_sum _ (fun j _ => Real.continuous_exp.comp (continuous_apply j))
    · intro y; exact ne_of_gt (softmax_denom_pos y)

/-! ## Key SimplexMap lemmas -/

/-- Every component of a SimplexMap output is at most 1. -/
theorem SimplexMap.le_one {n : ℕ} {φ : (Fin n → ℝ) → (Fin n → ℝ)} [SimplexMap φ]
    (x : Fin n → ℝ) (i : Fin n) : φ x i ≤ 1 := by
  have hsum := SimplexMap.sum_one (φ := φ) x
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => SimplexMap.nonneg x j) (Finset.mem_univ i)

/-- The output of a SimplexMap lies on the simplex. -/
theorem SimplexMap.mem_simplex {n : ℕ} {φ : (Fin n → ℝ) → (Fin n → ℝ)} [SimplexMap φ]
    (x : Fin n → ℝ) (i : Fin n) : 0 ≤ φ x i ∧ φ x i ≤ 1 :=
  ⟨SimplexMap.nonneg x i, SimplexMap.le_one x i⟩
