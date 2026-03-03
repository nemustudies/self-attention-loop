/-
  SleepLoop/Defs/BlendRate.lean

  Definition: Admissible blend rates (class L): continuous lambda : [0,1] -> [0,1]
  with lambda(0) = 1, lambda(1) = 0, and lambda(r) > 0 on [0,1).
  Paper: §2.1 (setup paragraph); boundary conditions forced by Proposition 7.
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-! ## Blend Rate -/

/-- An admissible blend rate in the class L.
    Boundary conditions lambda(0) = 1, lambda(1) = 0 are forced.
    Paper: Proposition 7a (prop:consolidation_rigidity). -/
structure BlendRate where
  fn : ℝ → ℝ
  maps_to : ∀ r, 0 ≤ r → r ≤ 1 → 0 ≤ fn r ∧ fn r ≤ 1
  at_zero : fn 0 = 1
  at_one : fn 1 = 0
  pos_interior : ∀ r, 0 ≤ r → r < 1 → 0 < fn r
  continuous_fn : Continuous fn

/-- The canonical (linear) blend rate: lambda(r) = 1 - r.
    This is the unique admissible blend rate for which
    lambda(r)/(1-r) = 1 is constant.
    Paper: Remark 8 (rem:invariance). -/
noncomputable def linearBlendRate : BlendRate where
  fn := fun r => 1 - r
  maps_to := fun r hr0 hr1 => ⟨by linarith, by linarith⟩
  at_zero := by norm_num
  at_one := by norm_num
  pos_interior := fun r _ hr1 => by linarith
  continuous_fn := continuous_const.sub continuous_id

/-- Alias: standard blend rate = linear blend rate -/
noncomputable abbrev BlendRate.standard := linearBlendRate

/-- Apply a blend rate to a ratio. -/
noncomputable def BlendRate.apply (br : BlendRate) (r : ℝ) : ℝ := br.fn r
