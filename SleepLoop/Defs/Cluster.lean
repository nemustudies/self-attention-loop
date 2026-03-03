/-
  SleepLoop/Defs/Cluster.lean

  Definition: Multi-cluster memory analysis structures.
  Epsilon-clusters under a query, and inter-cluster separation parameter.
  Paper: Definition 48 (def:cluster), Definition 49 (def:cluster_salience),
         Definition 54 (def:inter_cluster_sep), §3.6-3.7.
-/
import SleepLoop.Defs.DerivedQuantities

/-! ## Cluster Definitions -/

variable {d : ℕ}

/-- An ε-cluster under query q: a subset C ⊆ M such that
    max_{i,j ∈ C} |q · m_i - q · m_j| < ε.
    Paper: Definition 48 (def:cluster). -/
structure EpsCluster {n : ℕ}
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (ε : ℝ) where
  members : Finset (Fin n)
  nonempty : members.Nonempty
  clustered : ∀ i ∈ members, ∀ j ∈ members,
    |edot q (M i) - edot q (M j)| < ε

/-- Inter-cluster separation parameter: δ = min_{k≠k'} |q·c_k - q·c_{k'}|.
    Paper: Definition 54 (def:inter_cluster_sep). -/
noncomputable def interClusterSep
    {p : ℕ} (q : EuclideanSpace ℝ (Fin d))
    (centroids : Fin p → EuclideanSpace ℝ (Fin d)) : ℝ :=
  let pairs := (Finset.univ : Finset (Fin p × Fin p)).filter (fun pair => pair.1 ≠ pair.2)
  if h : pairs.Nonempty then
    Finset.inf' pairs h (fun pair => |edot q (centroids pair.1) - edot q (centroids pair.2)|)
  else
    0
