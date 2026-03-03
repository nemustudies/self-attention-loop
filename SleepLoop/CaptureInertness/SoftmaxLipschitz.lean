/-
  SleepLoop/CaptureInertness/SoftmaxLipschitz.lean

  Lemma 81 (lem:softmax_lipschitz): Softmax Lipschitz bound.
  For any x, y in R^n: ||phi(x) - phi(y)||_1 <= 2 ||x - y||_inf.
  Uses the Jacobian J = diag(phi) - phi phi^T and the mean value theorem.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Finset BigOperators MeasureTheory intervalIntegral

/-! ## Softmax Lipschitz Bound -/

variable {n : ℕ}

/-- The L¹ norm of a vector in Fin n → ℝ. -/
noncomputable def l1Norm (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i|

/-- The L∞ norm of a vector in Fin n → ℝ. -/
noncomputable def linfNorm [NeZero n] (x : Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun i => |x i|)

/-! ## Auxiliary lemmas for linfNorm -/

/-- Every component is bounded by linfNorm. -/
lemma linfNorm_le [NeZero n] (v : Fin n → ℝ) (i : Fin n) :
    |v i| ≤ linfNorm v := by
  unfold linfNorm
  exact Finset.le_sup' (fun i => |v i|) (Finset.mem_univ i)

/-- linfNorm is nonneg. -/
lemma linfNorm_nonneg [NeZero n] (v : Fin n → ℝ) :
    0 ≤ linfNorm v := by
  unfold linfNorm
  apply le_trans _ (Finset.le_sup' (fun i => |v i|) Finset.univ_nonempty.choose_spec)
  exact abs_nonneg _

/-- Paper: lem:softmax_lipschitz (auxiliary -- Jacobian operator norm bound).
    The softmax Jacobian operator norm ||J(z)||_{inf -> 1} <= 2.
    J = diag(phi) - phi phi^T, so for any v in R^n:
    ||Jv||_1 = ||diag(phi)v - phi(phi^T v)||_1 <= 2 ||v||_inf. -/
theorem softmax_jacobian_norm_bound [NeZero n]
    (z : Fin n → ℝ)
    (v : Fin n → ℝ) :
    let φ := softmax z
    l1Norm (fun i => φ i * v i - φ i * (∑ j, φ j * v j))
      ≤ 2 * linfNorm v := by
  simp only []
  set φ := softmax z with hφ_def
  set S := ∑ j : Fin n, φ j * v j with hS_def
  have hφ_nn : ∀ i, 0 ≤ φ i := fun i => le_of_lt ((softmax_positiveSimplexMap (n := n)).pos z i)
  have hφ_sum : ∑ i : Fin n, φ i = 1 := (softmax_positiveSimplexMap (n := n)).sum_one z
  -- Factor φᵢ out: |φᵢ vᵢ - φᵢ S| = φᵢ |vᵢ - S|
  have step1 : l1Norm (fun i => φ i * v i - φ i * S) =
      ∑ i : Fin n, φ i * |v i - S| := by
    unfold l1Norm
    simp_rw [← mul_sub, abs_mul, abs_of_nonneg (hφ_nn _)]
  rw [step1]
  -- Bound |S| ≤ linfNorm v
  have hS_bound : |S| ≤ linfNorm v := by
    calc |S| = |∑ j : Fin n, φ j * v j| := rfl
    _ ≤ ∑ j : Fin n, |φ j * v j| := abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, φ j * |v j| := by simp_rw [abs_mul, abs_of_nonneg (hφ_nn _)]
    _ ≤ ∑ j : Fin n, φ j * linfNorm v := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (linfNorm_le v j) (hφ_nn j)
    _ = linfNorm v := by
        simp_rw [mul_comm (φ _) (linfNorm v), ← Finset.mul_sum, hφ_sum, mul_one]
  -- Triangle inequality: |a - b| ≤ |a| + |b|
  have h_tri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    calc |a - b| = |a + (-b)| := by ring_nf
      _ ≤ |a| + |-b| := abs_add_le a (-b)
      _ = |a| + |b| := by rw [abs_neg]
  -- Bound the sum via triangle inequality + Σφᵢ = 1
  calc ∑ i : Fin n, φ i * |v i - S|
      ≤ ∑ i : Fin n, φ i * (|v i| + |S|) := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (h_tri (v i) S) (hφ_nn i)
    _ = (∑ i : Fin n, φ i * |v i|) + (∑ i : Fin n, φ i) * |S| := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = (∑ i : Fin n, φ i * |v i|) + |S| := by rw [hφ_sum, one_mul]
    _ ≤ linfNorm v + linfNorm v := by
        gcongr
        · calc ∑ i : Fin n, φ i * |v i|
              ≤ ∑ i : Fin n, φ i * linfNorm v :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left (linfNorm_le v i) (hφ_nn i)
            _ = linfNorm v := by
                simp_rw [mul_comm (φ _) (linfNorm v), ← Finset.mul_sum, hφ_sum, mul_one]
    _ = 2 * linfNorm v := by ring

/-! ## Continuity of softmax along a segment -/

/-- The function t ↦ softmax(y + t*(x-y)) i is continuous. -/
private lemma continuous_softmax_segment [NeZero n]
    (x y : Fin n → ℝ) (i : Fin n) :
    Continuous (fun t : ℝ => softmax (fun k => y k + t * (x k - y k)) i) := by
  have hlin : ∀ j : Fin n, Continuous (fun t : ℝ => y j + t * (x j - y j)) :=
    fun j => continuous_const.add (continuous_id.mul continuous_const)
  have hexp : ∀ j : Fin n, Continuous (fun t : ℝ => Real.exp (y j + t * (x j - y j))) :=
    fun j => Real.continuous_exp.comp (hlin j)
  have hsum : Continuous (fun t : ℝ => ∑ j : Fin n, Real.exp (y j + t * (x j - y j))) :=
    continuous_finset_sum Finset.univ (fun j _ => hexp j)
  simp only [softmax]
  exact (hexp i).div hsum (fun t => ne_of_gt (softmax_denom_pos _))

/-- The Jacobian integrand t ↦ softmax(z(t))ᵢ * (δᵢ - Σⱼ softmax(z(t))ⱼ * δⱼ) is continuous. -/
private lemma continuous_jac_integrand [NeZero n]
    (x y : Fin n → ℝ) (i : Fin n) :
    Continuous (fun t : ℝ =>
      softmax (fun k => y k + t * (x k - y k)) i *
        ((x i - y i) - ∑ j : Fin n, softmax (fun k => y k + t * (x k - y k)) j * (x j - y j))) := by
  apply Continuous.mul
  · exact continuous_softmax_segment x y i
  · apply Continuous.sub
    · exact continuous_const
    · apply continuous_finset_sum; intro j _
      exact (continuous_softmax_segment x y j).mul continuous_const

/-! ## Derivative of softmax along a segment -/

/-- The derivative of t ↦ softmax(y + t*(x-y)) i at time t equals
    the i-th component of the Jacobian-vector product J(z(t))·(x-y). -/
private lemma hasDerivAt_softmax_coord [NeZero n]
    (x y : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s => softmax (fun k => y k + s * (x k - y k)) i)
      (softmax (fun k => y k + t * (x k - y k)) i *
        ((x i - y i) - ∑ j : Fin n,
          softmax (fun k => y k + t * (x k - y k)) j * (x j - y j))) t := by
  -- Write softmax(z(s))ᵢ = exp(zᵢ(s)) / D(s) where D(s) = Σⱼ exp(zⱼ(s))
  -- zⱼ(s) = y j + s * (x j - y j), so d/ds zⱼ = x j - y j
  -- d/ds exp(zⱼ(s)) = exp(zⱼ(s)) * (x j - y j)
  -- d/ds D(s) = Σⱼ exp(zⱼ(s)) * (x j - y j)
  -- d/ds [exp(zᵢ(s)) / D(s)]
  --   = [D(s) * exp(zᵢ(s)) * (x i - y i) - exp(zᵢ(s)) * Σⱼ exp(zⱼ(s)) * (x j - y j)] / D(s)²
  --   = exp(zᵢ(s)) / D(s) * [(x i - y i) - Σⱼ (exp(zⱼ(s)) / D(s)) * (x j - y j)]
  --   = softmax(z(s))ᵢ * [(x i - y i) - Σⱼ softmax(z(s))ⱼ * (x j - y j)]
  set δ := fun k => x k - y k
  set z := fun s (k : Fin n) => y k + s * δ k
  set D := fun s => ∑ j : Fin n, Real.exp (z s j) with hD_def
  -- Derivative of each zⱼ(s)
  have hzderiv : ∀ k, HasDerivAt (fun s => z s k) (δ k) t := by
    intro k
    have h1 : HasDerivAt (fun s => s * δ k) (1 * δ k) t :=
      (hasDerivAt_id' t).mul_const (δ k)
    simp only [one_mul] at h1
    -- Use hasDerivAt_const_add_iff: HasDerivAt (c + f ·) ↔ HasDerivAt f
    exact (hasDerivAt_const_add_iff (y k)).mpr h1
  -- Derivative of exp(zⱼ(s))
  have hexpderiv : ∀ k, HasDerivAt (fun s => Real.exp (z s k))
      (Real.exp (z t k) * δ k) t := by
    intro k
    exact (hzderiv k).exp
  -- Derivative of D(s)
  have hDderiv : HasDerivAt D (∑ j : Fin n, Real.exp (z t j) * δ j) t := by
    simp only [hD_def]
    exact HasDerivAt.fun_sum (fun k _ => hexpderiv k)
  -- D(t) > 0
  have hDpos : D t > 0 := softmax_denom_pos _
  have hDne : D t ≠ 0 := ne_of_gt hDpos
  -- Derivative of exp(zᵢ(s)) / D(s) by quotient rule
  have hquot : HasDerivAt (fun s => Real.exp (z s i) / D s)
      ((Real.exp (z t i) * δ i * D t - Real.exp (z t i) * (∑ j, Real.exp (z t j) * δ j)) / D t ^ 2)
      t := (hexpderiv i).fun_div hDderiv hDne
  -- The goal function equals exp(z·i) / D
  have hfun_eq : (fun s => softmax (fun k => y k + s * (x k - y k)) i) =
      (fun s => Real.exp (z s i) / D s) := rfl
  rw [hfun_eq]
  -- Show the derivative values are equal, then apply hquot
  -- softmax(z t) i * (δ i - Σⱼ softmax(z t) j * δ j)
  --   = (E_i / D t) * (δ i - Σⱼ (E_j / D t) * δ j)
  --   = (E_i * δ i * D t - E_i * Σⱼ E_j * δ j) / D t²
  have hDt_ne : D t ≠ 0 := ne_of_gt (softmax_denom_pos (z t))
  have hderiv_eq : softmax (z t) i *
      (δ i - ∑ j : Fin n, softmax (z t) j * δ j) =
      (Real.exp (z t i) * δ i * D t -
        Real.exp (z t i) * ∑ j, Real.exp (z t j) * δ j) / D t ^ 2 := by
    simp only [softmax]
    -- Pull (∑ ...)⁻¹ out of inner sum: ∑ j, (E_j / S) * δ j = (∑ j, E_j * δ j) / S
    have hDt_ne' : (∑ j : Fin n, Real.exp (z t j)) ≠ 0 := hDt_ne
    rw [show ∑ j : Fin n, Real.exp (z t j) / (∑ j, Real.exp (z t j)) * δ j =
        (∑ j : Fin n, Real.exp (z t j) * δ j) / (∑ j, Real.exp (z t j)) from by
      rw [Finset.sum_div]; congr 1; ext j; ring]
    field_simp
    ring
  rw [hderiv_eq]
  exact hquot

/-- Paper: lem:softmax_lipschitz (main).
    ||softmax(x) - softmax(y)||_1 <= 2 ||x - y||_inf.
    Proof via FTC: softmax(x)_i - softmax(y)_i = integral_0^1 J(z(t))_i . (x-y) dt,
    sum the absolute values, swap sum and integral, apply Jacobian bound. -/
theorem softmax_lipschitz [NeZero n]
    (x y : Fin n → ℝ) :
    l1Norm (fun i => softmax x i - softmax y i)
      ≤ 2 * linfNorm (fun i => x i - y i) := by
  set δ := fun k => x k - y k with hδ_def
  -- Integrand function: J_i(t) = softmax(z(t))ᵢ * (δᵢ - Σⱼ softmax(z(t))ⱼ * δⱼ)
  let J : Fin n → ℝ → ℝ := fun i t =>
    softmax (fun k => y k + t * δ k) i *
      (δ i - ∑ j : Fin n, softmax (fun k => y k + t * δ k) j * δ j)
  -- FTC: softmax(x)ᵢ - softmax(y)ᵢ = ∫₀¹ J_i(t) dt
  have h_ftc : ∀ i : Fin n,
      softmax x i - softmax y i = ∫ t in (0 : ℝ)..1, J i t := by
    intro i
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => softmax (fun k => y k + s * δ k) i) (J i t) t := by
      intro t _
      exact hasDerivAt_softmax_coord x y i t
    have hint : IntervalIntegrable (J i) MeasureTheory.volume 0 1 :=
      (continuous_jac_integrand x y i).intervalIntegrable 0 1
    have hval := integral_eq_sub_of_hasDerivAt hderiv hint
    -- evaluate at endpoints: g(1) = softmax x i, g(0) = softmax y i
    have h1 : softmax (fun k => y k + (1 : ℝ) * δ k) i = softmax x i := by
      congr 1; ext k; simp [hδ_def]
    have h0 : softmax (fun k => y k + (0 : ℝ) * δ k) i = softmax y i := by
      congr 1; ext k; simp
    simp only [h1, h0] at hval
    linarith
  -- Bound l1Norm
  unfold l1Norm
  -- Σᵢ |softmax x i - softmax y i|
  calc ∑ i : Fin n, |softmax x i - softmax y i|
      = ∑ i : Fin n, |∫ t in (0 : ℝ)..1, J i t| := by
          congr 1; ext i; rw [← h_ftc i]
    _ ≤ ∑ i : Fin n, ∫ t in (0 : ℝ)..1, |J i t| := by
          apply Finset.sum_le_sum; intro i _
          exact abs_integral_le_integral_abs zero_le_one
    _ = ∫ t in (0 : ℝ)..1, ∑ i : Fin n, |J i t| := by
          rw [← intervalIntegral.integral_finset_sum]
          intro i _
          exact (continuous_jac_integrand x y i).abs.intervalIntegrable 0 1
    _ ≤ ∫ t in (0 : ℝ)..1, 2 * linfNorm δ := by
          apply intervalIntegral.integral_mono_on zero_le_one
          · -- IntervalIntegrable for Σ|J_i|
            apply (continuous_finset_sum Finset.univ (fun i _ =>
              (continuous_jac_integrand x y i).abs)).intervalIntegrable
          · exact intervalIntegrable_const
          · intro t _
            -- Σᵢ |J_i(t)| ≤ 2 * linfNorm δ by softmax_jacobian_norm_bound
            have hbound := softmax_jacobian_norm_bound (fun k => y k + t * δ k) δ
            -- hbound: l1Norm (fun i => φᵢ * δᵢ - φᵢ * Σⱼ φⱼ * δⱼ) ≤ 2 * linfNorm δ
            -- Goal: Σᵢ |J i t| ≤ 2 * linfNorm δ
            -- J i t = φᵢ * (δᵢ - Σⱼ φⱼ * δⱼ) = φᵢ * δᵢ - φᵢ * Σⱼ φⱼ * δⱼ (by mul_sub)
            simp only [l1Norm] at hbound
            convert hbound using 2 with i
            simp only [J, mul_sub]
    _ = 2 * linfNorm δ := by
          rw [intervalIntegral.integral_const]
          simp

/-- Paper: lem:softmax_lipschitz (corollary).
    If inputs differ by at most epsilon in L-infinity, outputs
    differ by at most 2 epsilon in L1. -/
theorem softmax_lipschitz_eps [NeZero n]
    (x y : Fin n → ℝ) (ε : ℝ)
    (hε : linfNorm (fun i => x i - y i) ≤ ε) :
    l1Norm (fun i => softmax x i - softmax y i) ≤ 2 * ε := by
  calc l1Norm (fun i => softmax x i - softmax y i)
      ≤ 2 * linfNorm (fun i => x i - y i) := softmax_lipschitz x y
    _ ≤ 2 * ε := by linarith [linfNorm_nonneg (fun i => x i - y i)]
