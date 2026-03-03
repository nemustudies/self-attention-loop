/-
  SleepLoop/Defs/DerivedQuantities.lean

  Definition: Key derived quantities used throughout the paper:
  V(t) (Lyapunov function), D(t) (diameter), rho (retrieval concentration),
  g (score gap), |M*| (critical memory size).
  Paper: §2.1 (notation block after Definition 6).
-/
import SleepLoop.Defs.LoopState
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Finset BigOperators

/-! ## Derived Quantities -/

variable {d : ℕ}

/-- lemma: For n ≥ 2, erasing any element from univ leaves a nonempty set. -/
lemma erase_v_nonempty {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    (Finset.univ.erase v : Finset (Fin n)).Nonempty := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨a, b, hab⟩ := this
  by_cases hav : a = v
  · exact ⟨b, Finset.mem_erase.mpr ⟨fun h => hab (hav ▸ h.symm), Finset.mem_univ _⟩⟩
  · exact ⟨a, Finset.mem_erase.mpr ⟨hav, Finset.mem_univ _⟩⟩

/-- lemma: For n > 0, the product of univ with itself is nonempty. -/
lemma product_univ_nonempty {n : ℕ} (hn : 0 < n) :
    ((Finset.univ ×ˢ Finset.univ) : Finset (Fin n × Fin n)).Nonempty := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.Nonempty.product Finset.univ_nonempty Finset.univ_nonempty

/-- Lyapunov function: V = max_{j ≠ v} ‖m_j - v‖.
    Measures memory spread from the anchor.
    Paper: §2.1 (notation block). -/
noncomputable def lyapunovV
    {n : ℕ} (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) : ℝ :=
  Finset.sup' (Finset.univ.erase v)
    (erase_v_nonempty hn v)
    (fun j => ‖M j - M v‖)

/-- Diameter: D(M) = max_{i,j} ‖m_i - m_j‖.
    Anchor-independent measure of memory spread.
    Paper: §2.1 (notation block). -/
noncomputable def diameter
    {n : ℕ} (M : Fin n → EuclideanSpace ℝ (Fin d)) (hn : 0 < n) : ℝ :=
  Finset.sup' (Finset.univ ×ˢ Finset.univ)
    (product_univ_nonempty hn)
    (fun p => ‖M p.1 - M p.2‖)

/-- Retrieval concentration: ρ = max_j w_j.
    Paper: §2.1 (notation block). -/
noncomputable def retrievalConcentration
    {n : ℕ} (w : Fin n → ℝ) (hn : 0 < n) : ℝ :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Finset.sup' Finset.univ Finset.univ_nonempty w

/-- Score gap: g = q · m_v - max_{k ≠ v} q · m_k.
    Paper: §2.1 (notation block). -/
noncomputable def scoreGap
    {n : ℕ} (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (v : Fin n) (hn : 2 ≤ n) : ℝ :=
  edot q (M v) - Finset.sup' (Finset.univ.erase v)
    (erase_v_nonempty hn v)
    (fun k => (edot q (M k) : ℝ))

/-- Critical memory size: |M*| = 1 + (1-c)/c · exp(2R²).
    Paper: Theorem 39(iv) (thm:sleep_pressure). -/
noncomputable def criticalMemorySize (c R : ℝ) : ℝ :=
  1 + (1 - c) / c * Real.exp (2 * R ^ 2)
