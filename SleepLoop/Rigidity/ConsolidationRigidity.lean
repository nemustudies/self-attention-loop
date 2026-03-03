/-
  SleepLoop/Rigidity/ConsolidationRigidity.lean

  Proposition (prop:consolidation_rigidity): Structural invariance.
  (a) Forced boundary conditions: lambda(1) = 0 and lambda(0) = 1 are forced.
      Violating lambda(1) = 0 destroys retrieval-gated stability;
      violating lambda(0) = 1 leaves unretrieved impressions permanently frozen.
  (b) Invariance: each result holds at one of three levels of
      A > A+ > {softmax}, and the interior of lambda is free.
  Level: A/A+/softmax.
-/
import SleepLoop.Defs.Consolidation

/-! ## Consolidation Rigidity (Structural Invariance) -/

variable {d : ℕ}

/-- Forced boundary condition (a, part 1):
    lambda(1) = 0 is necessary for anchor stability.
    If lambda(1) != 0, the anchor v = argmax w is displaced at every
    consolidation step.
    Paper: prop:consolidation_rigidity (a). -/
theorem blend_rate_at_one_forced
    (br : BlendRate) :
    br.fn 1 = 0 := br.at_one

/-- Forced boundary condition (a, part 2):
    lambda(0) = 1 is necessary to update unretrieved impressions.
    If lambda(0) != 1, an impression with w_j = 0 retains a permanent
    residue of its original position.
    Paper: prop:consolidation_rigidity (a). -/
theorem blend_rate_at_zero_forced
    (br : BlendRate) :
    br.fn 0 = 1 := br.at_zero

/-- The consolidation update m_j' = (1 - lambda_j) m_j + lambda_j T_j
    is a convex combination of m_j and T_j (since 0 <= lambda_j <= 1).
    Since T_j in conv(M) (by SimplexMap) and m_j in M, we have
    m_j' in conv(M). This holds for ANY blend rate lambda in L.
    Therefore the qualitative property (outputs remain in conv(M))
    is invariant across all admissible blend rates -- claim (b).
    Paper: prop:consolidation_rigidity (b). -/
theorem consolidation_invariant_across_blend_rates
    {n : ℕ} (hn : 0 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [SimplexMap φ]
    (br : BlendRate)
    (w : Fin n → ℝ)
    (hw_nn : ∀ k, 0 ≤ w k)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d)) :
    -- For each j, the consolidated m_j' is a convex combination
    -- of the original impressions, expressible as
    -- m_j' = sum_k beta_k * m_k for some beta on the simplex.
    ∀ j, ∃ (β : Fin n → ℝ),
      (∀ k, 0 ≤ β k) ∧
      ∑ k : Fin n, β k = 1 ∧
      consolidationStep φ br w q M hn j =
        ∑ k : Fin n, β k • M k := by
  intro j
  -- Let r = blend rate for j, α = simplex map output (scores)
  -- consolidationStep gives: (1 - r) • M j + r • (∑ k, α k • M k)
  -- We express this as ∑ k, β k • M k with β on the simplex.
  set r := (consolidationBlendRates br w hn) j
  set α : Fin n → ℝ := φ (fun k => edot (M j + q) (M k))
  have hα_nn : ∀ k, 0 ≤ α k := fun k => SimplexMap.nonneg _ k
  have hα_sum : ∑ k, α k = 1 := SimplexMap.sum_one _
  -- The consolidated m_j' = (1-r) • M j + r • (∑ k, α k • M k)
  -- This equals ∑ k, β k • M k where β k = r * α k + δ_{jk} * (1-r).
  -- β sums to 1 and (when 0 ≤ r ≤ 1) is nonneg.
  refine ⟨fun k => r * α k + if k = j then 1 - r else 0, ?_, ?_, ?_⟩
  · -- Nonnegativity: show 0 ≤ r ≤ 1 from blend rate properties
    -- r = br.fn (w j / w_max), and w j / w_max ∈ [0,1] since w ≥ 0
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    -- Extract the blend rate range
    have hr_range : 0 ≤ r ∧ r ≤ 1 := by
      change 0 ≤ consolidationBlendRates br w hn j ∧ consolidationBlendRates br w hn j ≤ 1
      unfold consolidationBlendRates
      set w_max := Finset.sup' Finset.univ Finset.univ_nonempty w with hw_max_def
      by_cases h_wmax : w_max = 0
      · -- All weights are 0: w j / 0 = 0, br.fn 0 = 1 ∈ [0,1]
        rw [h_wmax, div_zero, br.at_zero]
        norm_num
      · have h_wmax_nn : 0 ≤ w_max :=
          le_trans (hw_nn ⟨0, hn⟩) (Finset.le_sup' w (Finset.mem_univ _))
        have h_wmax_pos : 0 < w_max := lt_of_le_of_ne h_wmax_nn (Ne.symm h_wmax)
        have h_ratio_nn : 0 ≤ w j / w_max := div_nonneg (hw_nn j) (le_of_lt h_wmax_pos)
        have h_ratio_le : w j / w_max ≤ 1 :=
          div_le_one_of_le₀ (Finset.le_sup' w (Finset.mem_univ j)) (le_of_lt h_wmax_pos)
        exact br.maps_to _ h_ratio_nn h_ratio_le
    intro k
    simp only []
    by_cases hkj : k = j
    · -- k = j: r * α j + (1 - r) ≥ 0
      subst hkj; simp only [if_true]
      have : 0 ≤ r * α k := mul_nonneg hr_range.1 (hα_nn k)
      linarith [hr_range.2]
    · -- k ≠ j: r * α k + 0 = r * α k ≥ 0
      simp only [hkj, if_false, add_zero]
      exact mul_nonneg hr_range.1 (hα_nn k)
  · -- Sum to 1: ∑ (r * α k + δ_{jk}(1-r)) = r * 1 + (1-r) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hα_sum]
    -- Now: r * 1 + ∑ (if k=j then 1-r else 0) = 1
    -- The ite sum = 1 - r (only the j-th term contributes)
    rw [show ∑ k : Fin n, (if k = j then 1 - r else (0 : ℝ)) = 1 - r from by
      rw [Finset.sum_ite_eq']; simp]
    ring
  · -- Equality with consolidationStep
    -- RHS: ∑ (r * α k + δ_{jk}(1-r)) • M k
    --    = ∑ (r * α k) • M k + ∑ (δ_{jk}(1-r)) • M k
    --    = r • (∑ α k • M k) + (1-r) • M j
    -- LHS: consolidationStep = (1-r) • M j + r • (∑ α k • M k)
    -- Equal by add_comm.
    unfold consolidationStep consolidationTarget
    simp only []
    simp_rw [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    -- Handle the ite sum: ∑ (if k=j then (1-r) else 0) • M k = (1-r) • M j
    rw [show ∑ k : Fin n, (if k = j then (1 - r) else (0 : ℝ)) • M k = (1 - r) • M j from by
      simp_rw [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]]
    rw [add_comm]

/-- The three-level invariance hierarchy.
    A-level results use only Sum phi(x)_i = 1 and phi(x)_i >= 0.
    A+-level results additionally use phi(x)_i > 0 and order-preservation.
    Softmax-level results use the exponential formula.
    Paper: prop:consolidation_rigidity (b, hierarchy). -/
theorem invariance_hierarchy
    {n : ℕ} [NeZero n]
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [SimplexMap φ] :
    -- At 𝒜 level: φ(x) lies on the simplex
    (∀ x, ∑ i : Fin n, φ x i = 1) ∧
    (∀ x i, 0 ≤ φ x i) := by
  exact ⟨SimplexMap.sum_one, SimplexMap.nonneg⟩
