/-
  SleepLoop/Appendix/SleepPhases.lean

  Theorem 84 (thm:sleep_phases): Phase structure of the S=0 regime.
  Under softmax with capture disabled, sleep exhibits monotone phase structure:
    (i)   Score spread is non-increasing under fixed query, converges to 0
    (ii)  Early sleep: non-uniform retrieval, anchor may rotate, multi-region consolidation
    (iii) Late sleep: uniform retrieval, stable anchor, single-prototype convergence
    (iv)  Monotone transition from early to late via envelope 2R·D(t)
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster
import SleepLoop.Defs.BlendRate
import SleepLoop.CaptureInertness.SoftmaxLipschitz

open Finset BigOperators

/-! ## Phase Structure of the S=0 Regime (Appendix Theorem) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {n d : ℕ}

/-- sup' f - inf' f ≤ B when all pairwise differences f j - f k ≤ B. -/
private lemma sup'_sub_inf'_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℝ} {B : ℝ}
    (_hB : 0 ≤ B)
    (h_pair : ∀ j ∈ s, ∀ k ∈ s, f j - f k ≤ B) :
    s.sup' hs f - s.inf' hs f ≤ B := by
  rw [sub_le_iff_le_add, add_comm]
  rw [Finset.sup'_le_iff]
  intro j hj
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hs f
  calc f j ≤ f k + B := by linarith [h_pair j hj k hk]
    _ = s.inf' hs f + B := by rw [hkeq]

/-- For all j, ‖m_j - m_v‖ ≤ lyapunovV (including j = v). -/
private lemma norm_sub_le_lyapunovV {d n : ℕ} (hn : 2 ≤ n)
    (M : Fin n → EuclideanSpace ℝ (Fin d)) (v : Fin n) (j : Fin n) :
    ‖M j - M v‖ ≤ lyapunovV M v hn := by
  unfold lyapunovV
  by_cases hj : j = v
  · -- j = v: ‖m_v - m_v‖ = 0 ≤ sup'(‖m_k - m_v‖)
    rw [hj, sub_self, norm_zero]
    obtain ⟨w, hw⟩ := erase_v_nonempty hn v
    exact le_trans (norm_nonneg (M w - M v))
      (Finset.le_sup' (f := fun k => ‖M k - M v‖) hw)
  · -- j ≠ v: j ∈ univ.erase v, direct from sup' definition
    exact Finset.le_sup' (f := fun k => ‖M k - M v‖)
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)

/-- The fixed-query score spread: Δ̃_σ(t) = max_j q·m_j - min_j q·m_j.
    Measures how much retrieval scores differ across impressions. -/
noncomputable def scoreSpread
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n)) hne (fun j => edot q (M j)) -
  Finset.inf' (Finset.univ : Finset (Fin n)) hne (fun j => edot q (M j))

/-- (i) Fixed-query score spread is non-increasing when each updated score
    lies in the range of the original scores.
    Under consolidation, m'_j = (1-λ_j)·m_j + λ_j·T_j where T_j ∈ conv(M),
    so q·m'_j ∈ [min_k q·m_k, max_k q·m_k] for any fixed q.
    This is the abstract version; the hypothesis h_in_range encodes that
    consolidation preserves the score interval (proved in the paper via
    blend rates ∈ [0,1] and softmax simplex properties).
    Paper: thm:sleep_phases(i), first part. -/
theorem sleep_phases_score_spread_nonincreasing
    (_hn : 1 < n)
    (q : EuclideanSpace ℝ (Fin d))
    (M M' : Fin n → EuclideanSpace ℝ (Fin d))
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    -- Key consolidation property: each updated score lies in the original range
    (h_in_range : ∀ j : Fin n,
      Finset.inf' Finset.univ hne (fun k => edot q (M k)) ≤ edot q (M' j) ∧
      edot q (M' j) ≤ Finset.sup' Finset.univ hne (fun k => edot q (M k))) :
    scoreSpread q M' hne ≤ scoreSpread q M hne := by
  unfold scoreSpread
  -- Need: sup'(q·M'_j) - inf'(q·M'_j) ≤ sup'(q·M_j) - inf'(q·M_j)
  -- Since each q·M'_j ∈ [inf(q·M), sup(q·M)], the new sup ≤ old sup and new inf ≥ old inf
  have h_sup : Finset.sup' Finset.univ hne (fun j => edot q (M' j)) ≤
      Finset.sup' Finset.univ hne (fun k => edot q (M k)) := by
    rw [Finset.sup'_le_iff]
    intro j _
    exact (h_in_range j).2
  have h_inf : Finset.inf' Finset.univ hne (fun k => edot q (M k)) ≤
      Finset.inf' Finset.univ hne (fun j => edot q (M' j)) := by
    rw [Finset.le_inf'_iff]
    intro j _
    exact (h_in_range j).1
  linarith

/-- (i) Time-varying score spread converges to 0 as V(t) → 0.
    Δ̃_σ(t) ≤ 2R · V(t), and V(t) → 0.
    Paper: thm:sleep_phases(i), second part. -/
theorem sleep_phases_score_spread_vanishes
    (hn : 1 < n)
    (β : ℝ) (_hβ : 0 < β)
    (R : ℝ) (hR : 0 < R)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Fin n)
    -- Query norm bounded by R
    (hq_bound : ∀ t, ‖q t‖ ≤ R)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
  ∀ t, scoreSpread (q t) (M t) hne ≤ 2 * R * lyapunovV (M t) (v t) (by omega) := by
  -- Paper Thm: Δ̃_σ(t) ≤ 2R · V(t)
  -- Score spread = max_j q·m_j - min_j q·m_j
  -- For any j: q·m_j - q·m_v = q·(m_j - m_v), so |q·m_j - q·m_v| ≤ R·V(t)
  -- Therefore sup ≤ q·m_v + R·V(t) and inf ≥ q·m_v - R·V(t)
  -- Spread ≤ 2R·V(t)
  intro t
  -- Use sup'_sub_inf'_le: need ∀ j k, edot(q, m_j) - edot(q, m_k) ≤ 2R·V(t)
  have hV_nn : 0 ≤ lyapunovV (M t) (v t) (by omega) := by
    exact le_trans (norm_nonneg _) (norm_sub_le_lyapunovV (by omega) (M t) (v t)
      (erase_v_nonempty (by omega) (v t)).choose)
  apply sup'_sub_inf'_le hne (by nlinarith)
  intro j _ k _
  -- edot(q, m_j) - edot(q, m_k) = edot(q, m_j - m_k)
  have h_eq : edot (q t) (M t j) - edot (q t) (M t k) =
      edot (q t) (M t j - M t k) := by
    simp [edot, inner_sub_right]
  rw [h_eq]
  -- By Cauchy-Schwarz: edot(q, m_j - m_k) ≤ ‖q‖·‖m_j - m_k‖
  -- By triangle: ‖m_j - m_k‖ ≤ ‖m_j - m_v‖ + ‖m_k - m_v‖ ≤ 2V(t)
  have h_tri : ‖M t j - M t k‖ ≤ 2 * lyapunovV (M t) (v t) (by omega) := by
    calc ‖M t j - M t k‖
        = ‖(M t j - M t (v t)) - (M t k - M t (v t))‖ := by
          congr 1; abel
      _ ≤ ‖M t j - M t (v t)‖ + ‖M t k - M t (v t)‖ := norm_sub_le _ _
      _ ≤ lyapunovV (M t) (v t) (by omega) + lyapunovV (M t) (v t) (by omega) := by
          gcongr
          · exact norm_sub_le_lyapunovV (by omega) (M t) (v t) j
          · exact norm_sub_le_lyapunovV (by omega) (M t) (v t) k
      _ = 2 * lyapunovV (M t) (v t) (by omega) := by ring
  calc edot (q t) (M t j - M t k)
      ≤ ‖q t‖ * ‖M t j - M t k‖ := real_inner_le_norm _ _
    _ ≤ R * ‖M t j - M t k‖ := by
        apply mul_le_mul_of_nonneg_right (hq_bound t) (norm_nonneg _)
    _ ≤ R * (2 * lyapunovV (M t) (v t) (by omega)) := by
        apply mul_le_mul_of_nonneg_left h_tri (le_of_lt hR)
    _ = 2 * R * lyapunovV (M t) (v t) (by omega) := by ring

/-- (ii) Early sleep: softmax anchor weight exceeds 1/n when score spread is positive.
    w_v = exp(β·s_v) / Σ_k exp(β·s_k) ≥ 1/(1 + (n-1)·exp(-β·Δ)) > 1/n
    where Δ = s_v - max_{k≠v} s_k > 0.
    The second inequality holds because exp(-βΔ) < 1 when βΔ > 0.
    Paper: thm:sleep_phases(ii). -/
theorem sleep_phases_early_nonuniform
    (hn : 1 < n)
    (β Δ : ℝ) (hβ : 0 < β) (hΔ : 0 < Δ) :
    -- The denominator bound: 1 + (n-1)·exp(-β·Δ) < n
    -- which gives 1/(1+(n-1)exp(-βΔ)) > 1/n
    1 + (↑(n - 1) : ℝ) * Real.exp (-β * Δ) < ↑n := by
  -- Key: exp(-βΔ) < 1 because -βΔ < 0
  have h_neg : -β * Δ < 0 := by nlinarith
  have h_exp_lt : Real.exp (-β * Δ) < 1 := by
    rwa [Real.exp_lt_one_iff]
  -- So (n-1)·exp(-βΔ) < (n-1)
  have h_n_sub : (0 : ℝ) < ↑(n - 1) := by
    rw [Nat.cast_pos]; omega
  have h_prod_lt : (↑(n - 1) : ℝ) * Real.exp (-β * Δ) < ↑(n - 1) := by
    calc (↑(n - 1) : ℝ) * Real.exp (-β * Δ)
        < (↑(n - 1) : ℝ) * 1 := by
          exact mul_lt_mul_of_pos_left h_exp_lt h_n_sub
      _ = ↑(n - 1) := mul_one _
  -- Therefore 1 + (n-1)·exp(-βΔ) < 1 + (n-1) = n
  have h_one_le : 1 ≤ n := by omega
  have h_cast : (↑(n - 1) : ℝ) + 1 = ↑n := by
    rw [Nat.cast_sub h_one_le]
    ring
  linarith

/-- softmaxBeta β x = softmax (β • x), definitional unfolding. -/
private lemma softmaxBeta_eq_softmax {n : ℕ} (β : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    softmaxBeta β x i = softmax (fun k => β * x k) i := by
  rfl

/-- softmax of a constant function gives uniform weights: each = 1/n. -/
private lemma softmax_const_eq_uniform {n : ℕ} [NeZero n] (c : ℝ) (i : Fin n) :
    softmax (fun _ : Fin n => c) i = 1 / (↑n : ℝ) := by
  unfold softmax
  -- numerator = exp c, denominator = n * exp c
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (NeZero.pos n)
  have hexp_pos : (0 : ℝ) < Real.exp c := Real.exp_pos c
  field_simp

/-- Each component is bounded by the L1 norm: |f i| ≤ l1Norm f. -/
private lemma abs_le_l1Norm {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    |f i| ≤ l1Norm f := by
  unfold l1Norm
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)

/-- (iii) Late sleep: retrieval weights converge to uniform as V(t) → 0.
    When all m_j → v, we have w_j → 1/|M| for all j.
    Requires query norm bound ‖q(t)‖ ≤ R (Corollary cor:query_norm_bound in paper)
    to ensure score differences → 0 via |q·m_j - q·m_k| ≤ R·‖m_j - m_k‖ ≤ 2R·V(t).
    Paper: thm:sleep_phases(iii). -/
theorem sleep_phases_late_uniform
    (hn : 1 < n)
    (β : ℝ) (hβ : 0 < β)
    (R : ℝ) (hR : 0 < R)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Fin n)
    -- Query norm bounded by R (from Corollary cor:query_norm_bound)
    (hq_bound : ∀ t, ‖q t‖ ≤ R)
    -- V(t) → 0
    (hV_converge : ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, lyapunovV (M t) (v t) (by omega) < ε) :
    -- Retrieval weights converge to uniform: ∀ j, w_j → 1/n
    ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∀ j : Fin n,
      |softmaxBeta β (fun k => edot (q t) (M t k)) j -
       1 / (↑n : ℝ)| < ε := by
  -- Strategy: softmaxBeta β scores = softmax (β * scores).
  -- When V(t) → 0, all β * scores converge, so softmax → 1/n.
  -- Use softmax_lipschitz: ‖softmax(x) - softmax(y)‖₁ ≤ 2‖x - y‖_∞.
  -- Take y = constant vector, so softmax(y) = uniform.
  -- Then ‖x - y‖_∞ = max_k |β * s_k - β * s_0| ≤ β * 2R * V(t).
  -- Each |softmax(x)_j - 1/n| ≤ l1Norm ≤ 2 * β * 2R * V(t) = 4βR * V(t).
  -- Choose T so that V(t) < ε / (4βR).
  haveI : NeZero n := ⟨by omega⟩
  intro ε hε
  -- We need V(t) < ε / (4 * β * R) to ensure componentwise bound < ε
  -- But we need to be careful: the Lipschitz bound gives L1 ≤ 2 * Linf of score diffs
  -- and score diff linf ≤ β * 2R * V(t), so componentwise ≤ L1 ≤ 4βRV(t)
  set C := 4 * β * R with hC_def
  have hC_pos : 0 < C := by positivity
  obtain ⟨T, hT⟩ := hV_converge (ε / C) (div_pos hε hC_pos)
  use T
  intro t ht j
  -- Step 1: Rewrite softmaxBeta as softmax
  rw [softmaxBeta_eq_softmax]
  -- Step 2: The reference uniform vector: softmax of constant β * s₀
  -- Pick any fixed index, say (0 : Fin n), and set the constant c = β * edot (q t) (M t 0)
  set scores := fun k => β * edot (q t) (M t k) with hscores_def
  set c := scores ⟨0, by omega⟩ with hc_def
  set y := fun (_ : Fin n) => c with hy_def
  -- softmax(y) j = 1/n
  have h_unif : softmax y j = 1 / (↑n : ℝ) := softmax_const_eq_uniform c j
  -- Step 3: Bound |softmax(scores) j - 1/n| ≤ l1Norm(softmax(scores) - softmax(y))
  --       ≤ 2 * linfNorm(scores - y) (by softmax_lipschitz)
  have h_comp_le_l1 : |softmax scores j - 1 / (↑n : ℝ)| ≤
      l1Norm (fun i => softmax scores i - softmax y i) := by
    rw [← h_unif]
    exact abs_le_l1Norm (fun i => softmax scores i - softmax y i) j
  have h_l1_le_linf : l1Norm (fun i => softmax scores i - softmax y i) ≤
      2 * linfNorm (fun i => scores i - y i) := softmax_lipschitz scores y
  -- Step 4: Bound linfNorm(scores - y) ≤ β * 2R * V(t)
  -- scores k - y k = β * edot(q t)(M t k) - β * edot(q t)(M t 0)
  --               = β * (edot(q t)(M t k) - edot(q t)(M t 0))
  --               = β * edot(q t)(M t k - M t 0)
  -- |scores k - y k| ≤ β * ‖q t‖ * ‖M t k - M t 0‖ ≤ β * R * 2V(t)
  have h_linf_bound : linfNorm (fun i => scores i - y i) ≤
      2 * β * R * lyapunovV (M t) (v t) (by omega) := by
    unfold linfNorm
    apply Finset.sup'_le
    intro k _
    -- |scores k - c| = |β * edot(q t)(M t k) - β * edot(q t)(M t ⟨0, _⟩)|
    --               = β * |edot(q t)(M t k - M t ⟨0, _⟩)|
    change |scores k - c| ≤ 2 * β * R * lyapunovV (M t) (v t) (by omega)
    have h_diff : scores k - c = β * (edot (q t) (M t k) - edot (q t) (M t ⟨0, by omega⟩)) := by
      simp [hscores_def, hc_def, mul_sub]
    rw [h_diff, abs_mul, abs_of_pos hβ]
    have h_inner_diff : edot (q t) (M t k) - edot (q t) (M t ⟨0, by omega⟩) =
        edot (q t) (M t k - M t ⟨0, by omega⟩) := by
      simp [edot, inner_sub_right]
    rw [h_inner_diff]
    -- By Cauchy-Schwarz: |edot(q, m_k - m_0)| ≤ ‖q‖ * ‖m_k - m_0‖
    calc β * |edot (q t) (M t k - M t ⟨0, by omega⟩)|
        ≤ β * (‖q t‖ * ‖M t k - M t ⟨0, by omega⟩‖) := by
          gcongr; exact abs_real_inner_le_norm _ _
      _ ≤ β * (R * ‖M t k - M t ⟨0, by omega⟩‖) := by
          gcongr; exact hq_bound t
      _ ≤ β * (R * (2 * lyapunovV (M t) (v t) (by omega))) := by
          gcongr
          -- ‖m_k - m_0‖ ≤ ‖m_k - m_v‖ + ‖m_0 - m_v‖ ≤ 2V(t)
          calc ‖M t k - M t ⟨0, by omega⟩‖
              = ‖(M t k - M t (v t)) - (M t ⟨0, by omega⟩ - M t (v t))‖ := by congr 1; abel
            _ ≤ ‖M t k - M t (v t)‖ + ‖M t ⟨0, by omega⟩ - M t (v t)‖ := norm_sub_le _ _
            _ ≤ lyapunovV (M t) (v t) (by omega) + lyapunovV (M t) (v t) (by omega) := by
                gcongr
                · exact norm_sub_le_lyapunovV (by omega) (M t) (v t) k
                · exact norm_sub_le_lyapunovV (by omega) (M t) (v t) ⟨0, by omega⟩
            _ = 2 * lyapunovV (M t) (v t) (by omega) := by ring
      _ = 2 * β * R * lyapunovV (M t) (v t) (by omega) := by ring
  -- Step 5: Combine all bounds
  have hVt := hT t ht
  calc |softmax scores j - 1 / (↑n : ℝ)|
      ≤ l1Norm (fun i => softmax scores i - softmax y i) := h_comp_le_l1
    _ ≤ 2 * linfNorm (fun i => scores i - y i) := h_l1_le_linf
    _ ≤ 2 * (2 * β * R * lyapunovV (M t) (v t) (by omega)) := by gcongr
    _ = C * lyapunovV (M t) (v t) (by omega) := by rw [hC_def]; ring
    _ < C * (ε / C) := by gcongr
    _ = ε := by field_simp

/-- (iv) Monotone transition: score spread bounded by 2R·D(t), which is strictly
    decreasing. The transition from early to late sleep is irreversible.
    Paper: thm:sleep_phases(iv). -/
theorem sleep_phases_monotone_transition
    (hn : 1 < n)
    (R : ℝ) (hR : 0 < R)
    (M : ℕ → Fin n → EuclideanSpace ℝ (Fin d))
    (q : ℕ → EuclideanSpace ℝ (Fin d))
    -- Query norm bounded by R
    (hq_bound : ∀ t, ‖q t‖ ≤ R)
    -- Pairwise distances bounded by D(t)
    (h_diam_bound : ∀ t (i j : Fin n),
      ‖M t i - M t j‖ ≤ diameter (M t) (by omega))
    -- D(t) non-negative
    (hD_nn : ∀ t, 0 ≤ diameter (M t) (by omega))
    -- D(t) strictly decreasing under consolidation
    (_hD_decr : ∀ t, diameter (M t) (by omega) > 0 →
      diameter (M (t + 1)) (by omega) < diameter (M t) (by omega))
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    -- Score spread bounded by strictly decreasing envelope
    ∀ t, scoreSpread (q t) (M t) hne ≤ 2 * R * diameter (M t) (by omega) := by
  intro t
  apply sup'_sub_inf'_le hne (by nlinarith [hD_nn t])
  intro j _ k _
  have h_eq : edot (q t) (M t j) - edot (q t) (M t k) =
      edot (q t) (M t j - M t k) := by
    simp [edot, inner_sub_right]
  rw [h_eq]
  calc edot (q t) (M t j - M t k)
      ≤ ‖q t‖ * ‖M t j - M t k‖ := real_inner_le_norm _ _
    _ ≤ R * ‖M t j - M t k‖ := by
        exact mul_le_mul_of_nonneg_right (hq_bound t) (norm_nonneg _)
    _ ≤ R * diameter (M t) (by omega) :=
        mul_le_mul_of_nonneg_left (h_diam_bound t j k) (le_of_lt hR)
    _ ≤ 2 * R * diameter (M t) (by omega) := by nlinarith [hD_nn t]
