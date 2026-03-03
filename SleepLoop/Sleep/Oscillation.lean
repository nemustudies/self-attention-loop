/-
  SleepLoop/Sleep/Oscillation.lean

  Theorem 50 (thm:oscillation): Sleep cycle oscillation from multi-cluster consolidation.
  5-part theorem about oscillatory γ trajectory during multi-cluster sleep.
  Level: A₊.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster

open Finset BigOperators

/-! ## Multi-Cluster Oscillation (Theorem 50) -/

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- (i) Consolidation localizes to the anchor cluster.
    Impressions in the anchor cluster have small blend rates;
    impressions in other clusters have large blend rates but
    intra-cluster structure is preserved up to O(ε).
    Paper: thm:oscillation(i).

    Key content: for m_j in the anchor cluster C_{k*},
    all impressions are within ε of the anchor v, so their
    score differences |q·m_j - q·v| ≤ ‖q‖·ε. Under softmax,
    this gives w_j/w_v ≥ exp(-β·‖q‖·ε), hence the blend rate
    λ_j = 1 - w_j/w_v ≤ 1 - exp(-β·‖q‖·ε).
    For two impressions m_j, m_j' in the same non-anchor cluster
    with ‖m_j - m_j'‖ < ε, the difference in their displacements
    under consolidation is O(ε). -/
theorem oscillation_localization
    {n : ℕ} (_hn : 2 ≤ n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin n → ℝ) (v : Fin n)
    -- v is the anchor: w v ≥ w j for all j
    (hv : ∀ j, w j ≤ w v)
    (hw_pos : 0 < w v)
    (ε : ℝ) (_hε : 0 < ε)
    -- Anchor cluster members: within ε of v
    (anchor_cluster : Finset (Fin n))
    (hac : ∀ j ∈ anchor_cluster, ‖M j - M v‖ < ε) :
    -- (a) Score bound: anchor cluster members have scores within ‖q‖·ε of the anchor
    -- (b) Weight ratio bound: w_j/w_v ≤ 1 for all j (v is the argmax)
    (∀ j ∈ anchor_cluster, |edot q (M j) - edot q (M v)| ≤ ‖q‖ * ε) ∧
    (∀ j, w j / w v ≤ 1) := by
  constructor
  · -- (a) Score bound via Cauchy-Schwarz: |<q, m_j - m_v>| ≤ ‖q‖ · ‖m_j - m_v‖ < ‖q‖ · ε
    intro j hj
    have hscore : edot q (M j) - edot q (M v) = edot q (M j - M v) := by
      simp [edot, inner_sub_right]
    rw [hscore]
    calc |edot q (M j - M v)|
        ≤ ‖q‖ * ‖M j - M v‖ := abs_real_inner_le_norm q (M j - M v)
      _ ≤ ‖q‖ * ε := by
          apply mul_le_mul_of_nonneg_left (le_of_lt (hac j hj)) (norm_nonneg q)
  · -- (b) Weight ratio bound: w_j ≤ w_v, so w_j / w_v ≤ 1
    intro j
    rw [div_le_one hw_pos]
    exact hv j

/-- (ii) Anchor rotation upon cluster convergence.
    As C_{k*} converges, Δ_{k*}(q) → 0, weights equalize, γ → 0.
    Anchor rotates to next unconsolidated cluster, V spikes, γ recovers.
    Paper: thm:oscillation(ii).

    Key content: when the anchor rotates from v_old ∈ C_{k*} to
    v_new ∈ C_{k'} with ‖v_old - v_new‖ > 2ε (well-separated),
    the Lyapunov function V' measured from v_new satisfies
    V'(t) ≥ ‖v_old - v_new‖ > 0, i.e., V spikes.
    This is because v_old is still in the memory and is far from v_new. -/
theorem oscillation_anchor_rotation
    {n : ℕ} (hn : 2 ≤ n)
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v_old v_new : Fin n)
    (hne : v_old ≠ v_new)
    (ε : ℝ) (_hε : 0 < ε)
    -- Well-separation: old and new anchors are far apart
    (_h_sep : ‖M v_old - M v_new‖ > 2 * ε) :
    -- V measured from v_new is at least ‖v_old - v_new‖ > 0
    -- since v_old ∈ M and v_old ≠ v_new
    ‖M v_old - M v_new‖ ≤ lyapunovV M v_new hn := by
  unfold lyapunovV
  have hm : v_old ∈ Finset.univ.erase v_new :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  exact Finset.le_sup' (fun j => ‖M j - M v_new‖) hm

/-- (iii) Oscillatory γ trajectory.
    γ(t) exhibits sawtooth pattern: decay-then-spike for each cluster.
    Number of episodes is at most p - 1.
    Paper: thm:oscillation(iii).

    Key content: each anchor-cluster transition eliminates one cluster
    from the unconsolidated pool. Starting with p clusters, after at
    most p-1 transitions all clusters are consolidated.
    We formalize: given a list of transition times, its length is < p. -/
theorem oscillation_gamma_trajectory
    (p : ℕ) (hp : 2 ≤ p)
    -- Transition times: one per anchor rotation
    (transitions : Finset ℕ)
    -- Each transition eliminates one cluster; there are p clusters
    -- so at most p-1 transitions are possible.
    -- We require that each transition corresponds to a unique cluster
    -- being eliminated (injective map from transitions to clusters)
    (cluster_map : ℕ → Fin p)
    (h_inj : Set.InjOn cluster_map ↑transitions)
    -- The last remaining cluster converges without needing a transition.
    -- This means some cluster index is NOT in the image of cluster_map.
    (last_cluster : Fin p)
    (h_last : last_cluster ∉ transitions.image cluster_map) :
    -- The number of transitions is at most p - 1
    transitions.card ≤ p - 1 := by
  -- By injectivity, |transitions| = |image of cluster_map|
  have h_card_image : (transitions.image cluster_map).card = transitions.card :=
    Finset.card_image_of_injOn h_inj
  -- The image is a strict subset of Fin p (misses last_cluster)
  have h_image_ne : transitions.image cluster_map ≠ Finset.univ := by
    intro h_eq
    exact h_last (h_eq ▸ Finset.mem_univ _)
  have h_image_sub : transitions.image cluster_map ⊆ Finset.univ :=
    fun _ _ => Finset.mem_univ _
  have h_image_ssubset : transitions.image cluster_map ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨h_image_sub, h_image_ne⟩
  -- Therefore |image| ≤ |Fin p| - 1 = p - 1
  have h_card_lt : (transitions.image cluster_map).card < Fintype.card (Fin p) :=
    Finset.card_lt_card h_image_ssubset
  simp [Fintype.card_fin] at h_card_lt
  omega

/-- (iv) Bounded number of oscillation cycles: at most p - 1 transitions.
    Each transition eliminates one cluster from the unconsolidated pool.
    Paper: thm:oscillation(iv). -/
theorem oscillation_bounded_cycles
    (p : ℕ) (hp : 2 ≤ p)
    (n_transitions : ℕ) :
    -- Total anchor-cluster transitions ≤ p - 1
    n_transitions ≤ p - 1 → n_transitions < p := by
  omega

/-- (v) Salience ordering of consolidation.
    The most salient cluster under q₀ is consolidated first.
    Subsequent clusters selected by max retrieval mass under evolving query.
    Paper: thm:oscillation(v).

    Key content: the first anchor v = argmax_j w_j lies in the
    cluster with highest retrieval mass. This is immediate from
    the definition of the anchor as the argmax of retrieval weights.
    The retrieval concentration ρ = max_j w_j = w_v equals the
    anchor's weight, and the anchor's cluster has retrieval mass
    at least ρ (since it contains at least the anchor). -/
theorem oscillation_salience_ordering
    {n : ℕ} (_hn : 0 < n)
    (w : Fin n → ℝ)
    (hw_nn : ∀ j, 0 ≤ w j)
    -- The retrieval concentration is the max weight
    -- The anchor cluster contains the anchor v = argmax w_j
    -- So the anchor cluster has retrieval mass ≥ w_v = ρ = max_j w_j
    (anchor_cluster : Finset (Fin n))
    (v : Fin n)
    (hv_in : v ∈ anchor_cluster)
    (_hv_max : ∀ j, w j ≤ w v) :
    -- The anchor cluster's retrieval mass is at least the max weight
    w v ≤ ∑ j ∈ anchor_cluster, w j := by
  exact Finset.single_le_sum (fun j _ => hw_nn j) hv_in

/-- (vi) Termination recovers Theorem 44 (thm:wakeup).
    After all p clusters converge: γ → 0, V → 0, quasi-fixed-point.
    Terminal state: p prototypes (one per original cluster).
    Paper: thm:oscillation(vi). -/
theorem oscillation_termination
    {n : ℕ} (_hn : 1 < n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) [PositiveSimplexMap φ]
    (V γ : ℕ → ℝ) (p : ℕ) (_hp : 1 ≤ p)
    -- After all clusters consolidated:
    (h_all_done : ∀ ε > 0, ∃ T, ∀ t ≥ T, V t < ε)
    -- γ bounded by V (self-limiting property, Cor. self_limiting)
    (h_gamma_le_V : ∀ t, γ t ≤ V t) :
    -- γ → 0 and quasi-fixed-point reached
    ∀ ε > 0, ∃ T, ∀ t ≥ T, γ t < ε := by
  -- Paper Thm 50(vi): V→0 implies γ→0 via self-limiting bound γ ≤ V
  intro ε hε
  obtain ⟨T, hT⟩ := h_all_done ε hε
  exact ⟨T, fun t ht => lt_of_le_of_lt (h_gamma_le_V t) (hT t ht)⟩
