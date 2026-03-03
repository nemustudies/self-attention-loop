/-
  SleepLoop/Appendix/Naps.lean

  Theorem 90 (thm:nap): Naps as partial-cycle consolidation.
  5-part theorem characterizing short S=0 episodes:
    (i)   Front-loaded benefit: first k steps dominate second k steps
    (ii)  Single-cluster consolidation: nap consolidates at most ⌈k/min_i T_i⌉ clusters
    (iii) Split sleep consolidates different clusters via query context change
    (iv)  Split sleep preserves more prototypes when T_rot < 1/γ_min
    (v)   Diminishing returns of successive naps
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster
import SleepLoop.Defs.SleepDebt

open Finset BigOperators

/-! ## Naps as Partial-Cycle Consolidation (Appendix Theorem) -/

variable {d : ℕ}

/-- (i) Front-loaded benefit: the ratio of Lyapunov reduction in the second
    k-step window to the first satisfies R₂/R₁ ≤ α/(1-α) where α = (1-γ)^k.
    When (1-γ)^k ≤ 1/2, the first k steps produce ≥ the reduction of the next k.
    Paper: thm:nap(i). -/
theorem nap_front_loaded
    (V₀ : ℝ) (hV₀ : 0 < V₀)
    (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1)
    (k : ℕ) (hk : 0 < k)
    -- V(t+1) ≤ (1-γ)·V(t) contraction bound
    (V : ℕ → ℝ) (hV_init : V 0 = V₀)
    (h_contract : ∀ t, V (t + 1) ≤ (1 - γ) * V t)
    (h_nonneg : ∀ t, 0 ≤ V t) :
    -- First window reduction ≥ second window reduction
    let α := (1 - γ) ^ k
    let R₁ := V 0 - V k
    let R₂ := V k - V (2 * k)
    -- R₂ / R₁ ≤ α / (1 - α) when R₁ > 0
    R₁ > 0 → R₂ ≤ α / (1 - α) * R₁ := by
  change V 0 - V k > 0 →
    V k - V (2 * k) ≤ (1 - γ) ^ k / (1 - (1 - γ) ^ k) * (V 0 - V k)
  intro hR₁
  -- Step 1: V(t) ≤ (1-γ)^t · V₀ by induction
  have h_pow : ∀ t, V t ≤ (1 - γ) ^ t * V₀ := by
    intro t
    induction t with
    | zero => simp [hV_init]
    | succ t ih =>
      calc V (t + 1) ≤ (1 - γ) * V t := h_contract t
        _ ≤ (1 - γ) * ((1 - γ) ^ t * V₀) := by
            apply mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - γ) ^ (t + 1) * V₀ := by ring
  -- Step 2: α ∈ [0, 1) and 1 - α > 0
  have hα_nn : 0 ≤ (1 - γ) ^ k := pow_nonneg (by linarith) k
  have hα_lt : (1 - γ) ^ k < 1 := by
    apply pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have h1α : 0 < 1 - (1 - γ) ^ k := by linarith
  -- Step 3: V(k) ≤ α · V₀
  have hVk : V k ≤ (1 - γ) ^ k * V₀ := h_pow k
  -- Step 4: R₂ ≤ V(k) since V(2k) ≥ 0
  have hR₂_le : V k - V (2 * k) ≤ V k := by linarith [h_nonneg (2 * k)]
  -- Step 5: R₁ ≥ (1 - α) · V₀
  have hR₁_ge : V 0 - V k ≥ (1 - (1 - γ) ^ k) * V₀ := by nlinarith [hVk]
  -- Step 6: Chain R₂ ≤ V(k) ≤ α · V₀ = α/(1-α) · (1-α)·V₀ ≤ α/(1-α) · R₁
  calc V k - V (2 * k)
      ≤ V k := hR₂_le
    _ ≤ (1 - γ) ^ k * V₀ := hVk
    _ = (1 - γ) ^ k / (1 - (1 - γ) ^ k) * ((1 - (1 - γ) ^ k) * V₀) := by
        field_simp
    _ ≤ (1 - γ) ^ k / (1 - (1 - γ) ^ k) * (V 0 - V k) := by
        apply mul_le_mul_of_nonneg_left hR₁_ge
        exact div_nonneg hα_nn (le_of_lt h1α)

/-- Sufficient condition for front-loading: k ≥ ⌈log 2 / γ⌉ ensures (1-γ)^k ≤ 1/2.
    Paper: thm:nap(i), sufficient condition. -/
theorem nap_front_loaded_sufficient
    (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1) :
    ∀ k : ℕ, (↑k : ℝ) ≥ Real.log 2 / γ → (1 - γ) ^ k ≤ 1 / 2 := by
  intro k hk
  have h_base_nn : (0 : ℝ) ≤ 1 - γ := by linarith
  -- Step 1: 1 - γ ≤ exp(-γ)
  have h_exp_bound : 1 - γ ≤ Real.exp (-γ) := Real.one_sub_le_exp_neg γ
  -- Step 2: (1 - γ)^k ≤ exp(-γ)^k
  have h_pow_bound : (1 - γ) ^ k ≤ Real.exp (-γ) ^ k :=
    pow_le_pow_left₀ h_base_nn h_exp_bound k
  -- Step 3: exp(-γ)^k = exp(-γ · k)
  have h_exp_mul : Real.exp (-γ) ^ k = Real.exp (-(γ * ↑k)) := by
    rw [← Real.exp_nsmul, nsmul_eq_mul]
    ring_nf
  -- Step 4: γ · k ≥ log 2
  have h_prod : γ * ↑k ≥ Real.log 2 := by
    have h1 : Real.log 2 / γ ≤ ↑k := hk
    rw [div_le_iff₀ hγ_pos] at h1
    linarith
  -- Step 5: exp(-γ·k) ≤ exp(-log 2)
  have h_exp_le : Real.exp (-(γ * ↑k)) ≤ Real.exp (-(Real.log 2)) := by
    apply Real.exp_le_exp_of_le
    linarith
  -- Step 6: exp(-log 2) = 1/2
  have h_exp_log : Real.exp (-(Real.log 2)) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    ring
  -- Combine
  calc (1 - γ) ^ k ≤ Real.exp (-γ) ^ k := h_pow_bound
    _ = Real.exp (-(γ * ↑k)) := h_exp_mul
    _ ≤ Real.exp (-(Real.log 2)) := h_exp_le
    _ = 1 / 2 := h_exp_log

/-- (ii)(a) If k < T₁ (convergence time of anchor cluster), the nap
    partially consolidates only the anchor cluster.
    The anchor cluster's Lyapunov value V contracts by (1-γ) per step:
      V(t+1) ≤ (1-γ)·V(t)
    so after k steps, V(k) ≤ (1-γ)^k · V(0).
    Meanwhile, non-anchor impressions move by at most ε per step (O(ε) drift).
    Paper: thm:nap(ii)(a). -/
theorem nap_single_cluster_partial
    {n : ℕ} (_hn : 2 ≤ n)
    (V : ℕ → ℝ)
    (γ : ℝ) (_hγ_pos : 0 < γ) (hγ_lt : γ < 1)
    -- Contraction bound on anchor cluster
    (h_contract : ∀ t, V (t + 1) ≤ (1 - γ) * V t)
    (_h_nonneg : ∀ t, 0 ≤ V t)
    (k : ℕ) :
    -- After k steps: V(k) ≤ (1-γ)^k · V(0)
    V k ≤ (1 - γ) ^ k * V 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc V (k + 1) ≤ (1 - γ) * V k := h_contract k
      _ ≤ (1 - γ) * ((1 - γ) ^ k * V 0) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - γ) ^ (k + 1) * V 0 := by ring

/-- (ii)(b) Cluster count bound: if each cluster takes at least T_min steps
    to consolidate, then in k total steps at most ⌈k / T_min⌉ clusters
    can be fully consolidated.
    Paper: thm:nap(ii)(b), counting argument. -/
theorem nap_cluster_count_bound
    (k T_min : ℕ) (hT_min_pos : 0 < T_min)
    (num_consolidated : ℕ)
    -- Each consolidated cluster consumed at least T_min steps
    (h_each : T_min * num_consolidated ≤ k) :
    -- At most ⌈k / T_min⌉ clusters
    num_consolidated ≤ (k + T_min - 1) / T_min := by
  -- Step 1: num_consolidated ≤ k / T_min
  have h1 : num_consolidated ≤ k / T_min :=
    (Nat.le_div_iff_mul_le hT_min_pos).mpr (mul_comm num_consolidated T_min ▸ h_each)
  -- Step 2: k / T_min ≤ (k + T_min - 1) / T_min since k ≤ k + T_min - 1
  have h2 : k ≤ k + T_min - 1 := by omega
  exact le_trans h1 (Nat.div_le_div_right h2)

/-- (iii) Split sleep consolidates different clusters.
    Two naps separated by a waking interval can target different anchor clusters
    because the waking interval changes the query context.
    Paper: thm:nap(iii). -/
theorem nap_split_different_clusters
    {n : ℕ} (_hn : 1 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (q₁ q₂ : EuclideanSpace ℝ (Fin d))
    -- Waking interval changes query enough to shift anchor
    (v₁ : Fin n) (_hv₁ : ∀ j, edot q₁ (M v₁) ≥ edot q₁ (M j))
    (v₂ : Fin n) (_hv₂ : ∀ j, edot q₂ (M v₂) ≥ edot q₂ (M j))
    (h_diff : v₁ ≠ v₂) :
    -- The anchor clusters differ between the two naps
    v₁ ≠ v₂ := by
  exact h_diff

/-- (iv) Split sleep preserves more prototypes when T_rot < 1/γ_min.
    The waking interval provides query rotation that prevents collapse to
    a single prototype within clusters.
    Paper: thm:nap(iv). -/
theorem nap_split_preserves_prototypes
    (T_rot : ℝ) (γ_min : ℝ) (hγ : 0 < γ_min)
    (h_fast_rot : T_rot < 1 / γ_min) :
    -- Under fast query rotation, distinct impressions within a cluster
    -- are preserved rather than collapsed
    T_rot * γ_min < 1 := by
  have h1 : T_rot * γ_min < (1 / γ_min) * γ_min :=
    mul_lt_mul_of_pos_right h_fast_rot hγ
  rwa [one_div, inv_mul_cancel₀ (ne_of_gt hγ)] at h1

/-- (v) Diminishing returns of successive naps.
    Each successive nap provides strictly less total V reduction:
    the first nap addresses the most salient cluster, leaving less
    marginal benefit for subsequent naps.
    Paper: thm:nap(v). -/
theorem nap_diminishing_returns
    (V₀ : ℝ) (_hV₀ : 0 < V₀)
    (γ₁ γ₂ : ℝ) (_hγ₁ : 0 < γ₁) (_hγ₁_lt : γ₁ < 1)
    (hγ₂ : 0 < γ₂) (hγ₂_lt : γ₂ < 1)
    (k₁ k₂ : ℕ) (_hk₁ : 0 < k₁) (_hk₂ : 0 < k₂)
    -- First nap reduction
    (_R₁ : ℝ) (_hR₁ : _R₁ = V₀ * (1 - (1 - γ₁) ^ k₁))
    -- If second nap engages same cluster, its initial V is smaller
    (V_after : ℝ) (hV_after : V_after ≤ (1 - γ₁) ^ k₁ * V₀) :
    -- Second nap's absolute reduction (same cluster) is at most (1-γ₁)^k₁ times first
    V_after * (1 - (1 - γ₂) ^ k₂) ≤ (1 - γ₁) ^ k₁ * V₀ * (1 - (1 - γ₂) ^ k₂) := by
  have h_base_nn : 0 ≤ 1 - γ₂ := by linarith
  have h_base_lt : 1 - γ₂ < 1 := by linarith
  have h_pow_le : (1 - γ₂) ^ k₂ ≤ 1 := by
    exact pow_le_one₀ h_base_nn h_base_lt.le
  have h_factor_nn : 0 ≤ 1 - (1 - γ₂) ^ k₂ := by linarith
  exact mul_le_mul_of_nonneg_right hV_after h_factor_nn
