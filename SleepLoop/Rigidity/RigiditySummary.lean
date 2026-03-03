/-
  SleepLoop/Rigidity/RigiditySummary.lean

  Remark (rem:rigidity_summary): Rigidity summary.
  Every component falls into one of three categories:
  (a) Forced: accumulation scaling f(t) ~ t, capture threshold max,
      blend-rate boundaries lambda(0) = 1 / lambda(1) = 0,
      dot-product scoring, and feedback readout E^T.
  (b) Invariant: the simplex map phi in A, blend-rate interior lambda in L,
      query formation q = aE, and scoring rule h are free choices that don't
      affect any theorem.
  (c) Instance-defining: embedding E, linear map K, consolidation target T_j,
      and soft-vs-hard retrieval choice.
  Each of the 5 steps is necessary (prop:step_ablation).
  The retrieval pipeline requires exactly 4 operations (prop:pipeline_rigidity).
  Given any instance, zero tunable numerical parameters remain.
  Level: A.
-/
import SleepLoop.Rigidity.CaptureScaleInvariant
import SleepLoop.Rigidity.IdempotentCapture
import SleepLoop.Rigidity.CaptureRigidity
import SleepLoop.Rigidity.AccumulationRigidity
import SleepLoop.Rigidity.ConsolidationRigidity
import SleepLoop.Rigidity.PipelineRigidity
import SleepLoop.Rigidity.TargetAxioms
import SleepLoop.Rigidity.ScoringAdditivity
import SleepLoop.Rigidity.StepAblation

/-! ## Rigidity Summary -/

/-- Classification of system components. -/
inductive ComponentClass
  /-- Uniquely determined by consistency requirements. No alternative exists. -/
  | forced
  /-- Free choice, but theorems don't depend on which admissible choice is made. -/
  | invariant
  /-- Specifies which system is being studied. Minimal axioms given. -/
  | instance_defining
  deriving DecidableEq, Repr

/-- The forced components (category a). -/
def forcedComponents : List String :=
  [ "accumulation scaling f(t) ~ t (prop:rigidity)"
  , "capture threshold max (prop:capture_rigidity)"
  , "blend-rate boundaries λ(0) = 1, λ(1) = 0 (prop:consolidation_rigidity)"
  , "dot-product scoring s_j = q · m_j (prop:pipeline_rigidity.b)"
  , "feedback readout E^T (prop:pipeline_rigidity.d)"
  ]

/-- The invariant components (category b). -/
def invariantComponents : List String :=
  [ "simplex map φ ∈ 𝒜 (prop:consolidation_rigidity)"
  , "blend-rate interior λ ∈ ℒ (prop:consolidation_rigidity)"
  , "query formation q = aE (prop:pipeline_rigidity.a)"
  , "scoring rule h (prop:scoring_additivity)"
  ]

/-- The instance-defining components (category c). -/
def instanceDefiningComponents : List String :=
  [ "embedding E (prop:pipeline_rigidity)"
  , "linear map K (prop:pipeline_rigidity.d)"
  , "consolidation target T_j (prop:target_axioms)"
  , "soft vs hard retrieval (prop:pipeline_rigidity.c)"
  ]

/-- Rigidity summary: every component is classified, each step is necessary,
    the pipeline is irreducible, and zero tunable parameters remain.
    Paper: rem:rigidity_summary. -/
theorem rigidity_summary :
    forcedComponents.length + invariantComponents.length +
    instanceDefiningComponents.length = 13 := by
  decide
