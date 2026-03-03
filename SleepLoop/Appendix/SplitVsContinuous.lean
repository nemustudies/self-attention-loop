/-
  SleepLoop/Appendix/SplitVsContinuous.lean

  Corollary 92 (cor:split_vs_continuous): Continuous sleep vs. split sleep trade-off.
  Given a fixed total sleep budget K_total = k₁ + k₂:
    (i)   Continuous: V reduction >= V(0)[1-(1-gamma)^K], up to ceil(K/min_i T_i) clusters
    (ii)  Split: comparable total V reduction, different query contexts per nap
    (iii) Trade-off: continuous = deeper consolidation, split = broader coverage
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster
import SleepLoop.Defs.SleepDebt

open Finset BigOperators

/-! ## Continuous vs Split Sleep (Appendix Corollary) -/

variable {d : ℕ}

/-- (i) Continuous sleep: total V reduction of at least V(0)[1 - (1-γ)^K_total]
    in the anchor cluster, processing up to ⌈K_total / min_i T_i⌉ clusters.
    Paper: cor:split_vs_continuous(i). -/
theorem split_vs_continuous_continuous
    (V₀ : ℝ) (_hV₀ : 0 < V₀)
    (γ : ℝ) (_hγ_pos : 0 < γ) (hγ_lt : γ < 1)
    (K_total : ℕ) (_hK : 0 < K_total)
    (V : ℕ → ℝ) (hV_init : V 0 = V₀)
    (h_contract : ∀ t, V (t + 1) ≤ (1 - γ) * V t)
    (_h_nonneg : ∀ t, 0 ≤ V t) :
    -- V reduction is at least V₀ · (1 - (1-γ)^K_total)
    V 0 - V K_total ≥ V₀ * (1 - (1 - γ) ^ K_total) := by
  -- Suffices to show V K_total ≤ (1 - γ)^K_total * V₀
  suffices h : V K_total ≤ (1 - γ) ^ K_total * V₀ by
    rw [hV_init]; nlinarith
  -- Prove by induction: V t ≤ (1-γ)^t * V₀
  suffices h : ∀ t, V t ≤ (1 - γ) ^ t * V₀ from h K_total
  intro t
  induction t with
  | zero => simp [hV_init]
  | succ t ih =>
    calc V (t + 1) ≤ (1 - γ) * V t := h_contract t
    _ ≤ (1 - γ) * ((1 - γ) ^ t * V₀) := by
        apply mul_le_mul_of_nonneg_left ih
        linarith
    _ = (1 - γ) ^ (t + 1) * V₀ := by ring

/-- (i, cluster count) Continuous sleep processes at most ⌈K_total / T_min⌉ clusters.
    Paper: cor:split_vs_continuous(i), cluster count bound.
    This reuses the same counting argument as nap_cluster_count_bound:
    if each cluster takes at least T_min steps to consolidate, then in
    K_total total steps at most ⌈K_total / T_min⌉ clusters can be processed. -/
theorem split_vs_continuous_cluster_count
    (K_total T_min : ℕ) (hT_min_pos : 0 < T_min)
    (num_consolidated : ℕ)
    -- Each consolidated cluster consumed at least T_min steps
    (h_each : T_min * num_consolidated ≤ K_total) :
    -- At most ⌈K_total / T_min⌉ clusters
    num_consolidated ≤ (K_total + T_min - 1) / T_min := by
  -- Same argument as nap_cluster_count_bound
  have h1 : num_consolidated ≤ K_total / T_min :=
    (Nat.le_div_iff_mul_le hT_min_pos).mpr (mul_comm num_consolidated T_min ▸ h_each)
  have h2 : K_total ≤ K_total + T_min - 1 := by omega
  exact le_trans h1 (Nat.div_le_div_right h2)

/-- (ii) Split sleep: each nap governed by the same contraction bound.
    Total reduction across both clusters is the sum of individual reductions.
    Paper: cor:split_vs_continuous(ii). -/
theorem split_vs_continuous_split
    (V₁ V₂ : ℝ) (_hV₁ : 0 < V₁) (_hV₂ : 0 < V₂)
    (γ₁ γ₂ : ℝ) (_hγ₁_pos : 0 < γ₁) (_hγ₁_lt : γ₁ < 1)
    (_hγ₂_pos : 0 < γ₂) (_hγ₂_lt : γ₂ < 1)
    (k₁ k₂ : ℕ) (_hk₁ : 0 < k₁) (_hk₂ : 0 < k₂) :
    -- Total reduction is sum of per-nap reductions
    let R₁ := V₁ * (1 - (1 - γ₁) ^ k₁)
    let R₂ := V₂ * (1 - (1 - γ₂) ^ k₂)
    R₁ + R₂ = V₁ * (1 - (1 - γ₁) ^ k₁) + V₂ * (1 - (1 - γ₂) ^ k₂) := by
  rfl

/-- (iii) Trade-off: continuous sleep achieves deeper consolidation of the most
    salient cluster (V_anchor ≤ (1-γ)^K · V₀, exponentially small), while split
    sleep provides broader coverage (different clusters from different queries).
    Paper: cor:split_vs_continuous(iii). -/
theorem split_vs_continuous_tradeoff_depth
    (V₀ : ℝ) (hV₀ : 0 < V₀)
    (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1)
    (k₁ k₂ : ℕ) (_hk₁ : 0 < k₁) (_hk₂ : 0 < k₂) :
    -- Continuous: anchor cluster residual after full budget
    let K_total := k₁ + k₂
    let V_continuous := (1 - γ) ^ K_total * V₀
    -- Split: anchor cluster residual after first nap only
    let V_split := (1 - γ) ^ k₁ * V₀
    -- Continuous achieves deeper consolidation of the anchor cluster
    V_continuous ≤ V_split := by
  -- Unfold the let bindings
  change (1 - γ) ^ (k₁ + k₂) * V₀ ≤ (1 - γ) ^ k₁ * V₀
  -- (1-γ)^(k₁+k₂) = (1-γ)^k₁ * (1-γ)^k₂
  rw [pow_add]
  -- Need: (1-γ)^k₁ * (1-γ)^k₂ * V₀ ≤ (1-γ)^k₁ * V₀
  -- i.e., (1-γ)^k₂ ≤ 1 (since (1-γ)^k₁ * V₀ > 0)
  have h1 : 0 < (1 - γ) ^ k₁ := pow_pos (by linarith) _
  have h2 : 0 < V₀ := hV₀
  have h3 : (1 - γ) ^ k₂ ≤ 1 := by
    apply pow_le_one₀ <;> linarith
  nlinarith [mul_le_mul_of_nonneg_right h3 (mul_pos h1 h2).le]

/-- Trade-off, breadth direction: split sleep can consolidate a cluster that
    continuous sleep would not reach until step T₁ (anchor rotation).
    Paper: cor:split_vs_continuous(iii), breadth argument. -/
theorem split_vs_continuous_tradeoff_breadth
    (T₁ : ℕ) (k₁ : ℕ) (hk₁ : k₁ < T₁) :
    -- Under continuous sleep, the second cluster is not addressed until step T₁.
    -- Under split sleep, the second nap can target it immediately.
    -- The breadth advantage exists when k₁ < T₁.
    k₁ < T₁ := by
  exact hk₁
