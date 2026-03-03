-- Root import file for SleepLoop
-- Formal verification of "A Math Loop That Sleeps and Dreams"

-- Layer 1: Definitions
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.BlendRate
import SleepLoop.Defs.Embedding
import SleepLoop.Defs.LoopState
import SleepLoop.Defs.Scoring
import SleepLoop.Defs.Observation
import SleepLoop.Defs.Accumulation
import SleepLoop.Defs.Retrieval
import SleepLoop.Defs.Consolidation
import SleepLoop.Defs.Capture
import SleepLoop.Defs.DerivedQuantities
import SleepLoop.Defs.Cluster
import SleepLoop.Defs.SleepDebt

-- Layer 2: Rigidity
import SleepLoop.Rigidity.CaptureScaleInvariant
import SleepLoop.Rigidity.IdempotentCapture
import SleepLoop.Rigidity.CaptureRigidity
import SleepLoop.Rigidity.AccumulationRigidity
import SleepLoop.Rigidity.ConsolidationRigidity
import SleepLoop.Rigidity.PipelineRigidity
import SleepLoop.Rigidity.TargetAxioms
import SleepLoop.Rigidity.ScoringAdditivity
import SleepLoop.Rigidity.StepAblation
import SleepLoop.Rigidity.RigiditySummary

-- Layer 3: Core Dynamics
import SleepLoop.Core.HistoryIndependence
import SleepLoop.Core.SelectivePersistence
import SleepLoop.Core.RetrievalGatedStability
import SleepLoop.Core.MonotoneAcquisition
import SleepLoop.Core.ConvexHullInvariance
import SleepLoop.Core.FiniteMemory
import SleepLoop.Core.BoundedBias
import SleepLoop.Core.NonDegeneracy
import SleepLoop.Core.RetrievalInHull
import SleepLoop.Core.QueryNormBound
import SleepLoop.Core.BlendRateBounds
import SleepLoop.Core.AttentionBudget
import SleepLoop.Core.Lyapunov
import SleepLoop.Core.ContractionRate
import SleepLoop.Core.FanEffect
import SleepLoop.Core.RetrievalWeightBounds
import SleepLoop.Core.Convergence
import SleepLoop.Core.SelfLimiting
import SleepLoop.Core.PrototypeFormation
import SleepLoop.Core.ContextVariation
import SleepLoop.Core.ForgettingCurve
import SleepLoop.Core.TestingEffect
import SleepLoop.Core.SpacingEffect
import SleepLoop.Core.RetrievalCrossover

-- Layer 4: Capture Inertness
import SleepLoop.CaptureInertness.CaptureArgmax
import SleepLoop.CaptureInertness.SoftmaxLipschitz
import SleepLoop.CaptureInertness.SigmaIncrement
import SleepLoop.CaptureInertness.FiniteArgmax
import SleepLoop.CaptureInertness.PerturbativeInertness
import SleepLoop.CaptureInertness.KZeroInertness
import SleepLoop.CaptureInertness.ForcedCycleGeneralK

-- Layer 5: Sleep
import SleepLoop.Sleep.RetrievalDegradation
import SleepLoop.Sleep.SleepEfficacy
import SleepLoop.Sleep.MonotonePressure
import SleepLoop.Sleep.Irreversibility
import SleepLoop.Sleep.Wakeup
import SleepLoop.Sleep.SelfObservable
import SleepLoop.Sleep.SleepWakeCycle
import SleepLoop.Sleep.Oscillation
import SleepLoop.Sleep.SleepDuration
import SleepLoop.Sleep.SleepDebtThm
import SleepLoop.Sleep.DebtObservable
import SleepLoop.Sleep.ScoreBoost
import SleepLoop.Sleep.DreamTransitions
import SleepLoop.Sleep.DreamAmnesia
import SleepLoop.Sleep.ForcedCycle
import SleepLoop.Sleep.SleepGate
import SleepLoop.Sleep.Insomnia
import SleepLoop.Sleep.Maturation

-- Layer 6: Appendix
import SleepLoop.Appendix.SleepPhases
import SleepLoop.Appendix.Naps
import SleepLoop.Appendix.SplitVsContinuous

-- Main theorem (Mathlib-only statement + proof + axiom audit)
import SleepLoop.MainTheorem
import SleepLoop.ProofOfMainTheorem
import SleepLoop.Verification
