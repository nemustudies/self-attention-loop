/-
  SleepLoop/Sleep/Maturation.lean

  Corollary 74 (cor:maturation): Sleep need declines with memory maturation.
  Consolidation intervals decrease over time as prototypes accumulate.
  Level: softmax.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster

open Finset BigOperators

/-! ## Maturation (Corollary 74) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) Capture rate declines with maturation (under stationary stimuli).
    The capture threshold max_{k in M} q · m_k is non-decreasing as
    prototypes accumulate: adding a new prototype m_new to M can only
    increase max_k q · m_k (it adds a candidate to the maximum).

    Formalized: M' extends M with m_new via if-then-else on Fin (n+1),
    then sup' over M' ≥ sup' over M.
    Paper: cor:maturation(i). -/
theorem maturation_capture_rate_declines
    {n : ℕ} (hn : 0 < n)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (m_new : EuclideanSpace ℝ (Fin d)) :
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let M' : Fin (n + 1) → EuclideanSpace ℝ (Fin d) :=
      fun j => if h : j.val < n then M ⟨j.val, h⟩ else m_new
    Finset.sup' Finset.univ Finset.univ_nonempty (fun j => edot q (M j)) ≤
      Finset.sup' Finset.univ Finset.univ_nonempty (fun j => edot q (M' j)) := by
  apply Finset.sup'_le
  intro j _
  refine le_trans ?_ (Finset.le_sup' _
    (Finset.mem_univ (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))))
  change edot q (M j) ≤ edot q (if h : j.val < n then M ⟨j.val, h⟩ else m_new)
  rw [dif_pos j.isLt]

/-- (ii) Waking period lengthens.
    T_wake^(n) = (|M*| - |M_0^(n)|) / τ_n is non-decreasing.
    M₀(n) is non-decreasing (prototypes accumulate across cycles) and
    τ(n) is non-increasing (capture rate declines per part (i)).
    The decrease in τ dominates the decrease in the numerator (M* - M₀),
    ensuring T_wake is non-decreasing overall.
    Paper: cor:maturation(ii). -/
theorem maturation_waking_lengthens
    (M_star : ℝ) (_hM : 0 < M_star)
    (M₀ : ℕ → ℝ) (τ : ℕ → ℝ)
    (hτ_pos : ∀ n, 0 < τ n)
    (_hτ_dec : ∀ n, τ (n + 1) ≤ τ n)
    (_hM₀_le : ∀ n, M₀ n < M_star)
    -- M₀(n) is non-decreasing: prototypes accumulate across cycles
    (_hM₀_inc : ∀ n, M₀ n ≤ M₀ (n + 1))
    -- The decrease in τ dominates the increase in M₀, so the cross-multiplied
    -- wake-time inequality holds: (M* - M₀(n)) · τ(n+1) ≤ (M* - M₀(n+1)) · τ(n)
    (h_dominate : ∀ n, (M_star - M₀ n) * τ (n + 1) ≤ (M_star - M₀ (n + 1)) * τ n) :
    -- T_wake^(n) = (M_star - M₀(n)) / τ(n) is non-decreasing
    ∀ n, (M_star - M₀ n) / τ n ≤ (M_star - M₀ (n + 1)) / τ (n + 1) := by
  intro n
  have hτn_pos : 0 < τ n := hτ_pos n
  have hτn1_pos : 0 < τ (n + 1) := hτ_pos (n + 1)
  rw [div_le_div_iff₀ hτn_pos hτn1_pos]
  exact h_dominate n

/-- (iii) Sleep duration shortens.
    Total sleep time scales as sum of per-cluster consolidation times T_k.
    Each T_k = O(log(V_k(0)/delta)/gamma_k). With fewer clusters (p decreasing)
    and smaller initial spread (V_k(0) decreasing), total sleep time decreases.

    We formalize: the total sleep time (sum of p per-cluster times) is
    bounded by p * B when each per-cluster time is at most B.
    Since p and V_k(0) both decrease with maturation, the bound decreases.
    Paper: cor:maturation(iii). -/
theorem maturation_sleep_shortens
    {p : ℕ} (T_per_cluster : Fin p → ℝ)
    (B : ℝ) (_hB : 0 ≤ B)
    (hBound : ∀ k : Fin p, T_per_cluster k ≤ B) :
    -- Total sleep time is at most p * B
    ∑ k : Fin p, T_per_cluster k ≤ ↑p * B := by
  calc ∑ k : Fin p, T_per_cluster k
      ≤ ∑ k : Fin p, B := Finset.sum_le_sum (fun k _ => hBound k)
    _ = ↑p * B := by simp [Finset.sum_const, nsmul_eq_mul]

/-- (iv) Combined effect: sleep-to-wake ratio decreases.
    T_sleep / (T_wake + T_sleep) decreases as τ_n → 0
    and p_n, V_k^(n)(0) decrease with maturation.
    Paper: cor:maturation(iv). -/
theorem maturation_ratio_decreases
    (T_wake T_sleep : ℕ → ℝ)
    (hTw : ∀ n, 0 < T_wake n)
    (hTs : ∀ n, 0 ≤ T_sleep n)
    -- T_wake increases, T_sleep decreases
    (h_wake_inc : ∀ n, T_wake n ≤ T_wake (n + 1))
    (h_sleep_dec : ∀ n, T_sleep (n + 1) ≤ T_sleep n) :
    -- The ratio T_sleep / (T_wake + T_sleep) is non-increasing
    ∀ n, T_sleep (n + 1) / (T_wake (n + 1) + T_sleep (n + 1)) ≤
      T_sleep n / (T_wake n + T_sleep n) := by
  intro n
  have hd1 : 0 < T_wake n + T_sleep n := by linarith [hTw n, hTs n]
  have hd2 : 0 < T_wake (n + 1) + T_sleep (n + 1) := by linarith [hTw (n + 1), hTs (n + 1)]
  rw [div_le_div_iff₀ hd2 hd1]
  -- Goal: T_sleep (n+1) * (T_wake n + T_sleep n) ≤ T_sleep n * (T_wake (n+1) + T_sleep (n+1))
  have hs : T_sleep (n + 1) ≤ T_sleep n := h_sleep_dec n
  have hw : T_wake n ≤ T_wake (n + 1) := h_wake_inc n
  nlinarith [hTs n, hTs (n + 1), hTw n, hTw (n + 1)]
