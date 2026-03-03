# SleepLoop Formalization

Lean 4 formal verification of **"A Math Loop That Sleeps and Dreams"**.

## Status

| Metric | Value |
|--------|-------|
| Sorries | **0** |
| Build jobs | 3,183 |
| Lean files | 80 |
| Lines of code | ~11,500 |
| Lint warnings | 342 (all cosmetic) |
| Sessions to complete | 6 |
| Initial sorry count | 178 |

## Module Structure

### Definitions (`Defs/`, 13 files)
Core type definitions and structures for the five-step loop.

| File | Description |
|------|-------------|
| `SimplexMap.lean` | PositiveSimplexMap typeclass (A-level maps with continuity) |
| `LoopState.lean` | Loop state: queries, weights, scores |
| `Accumulation.lean` | Generalized accumulation recurrence C(t+1) = C(t) + a(t)f(t)/C(t) |
| `Retrieval.lean` | Retrieval step definitions |
| `Scoring.lean` | Score functions and softmax |
| `Capture.lean` | Capture step definitions |
| `Consolidation.lean` | Consolidation step definitions |
| `SleepDebt.lean` | Sleep debt and pressure |
| `DerivedQuantities.lean` | sigma, gamma, rho derived from state |
| `BlendRate.lean` | Blend rate alpha definitions |
| `Observation.lean` | Observation step |
| `Embedding.lean` | Embedding maps |
| `Cluster.lean` | Cluster definitions |

### Core Dynamics (`Core/`, 20 files)
Main convergence and stability theorems.

| File | Key Theorems |
|------|-------------|
| `Convergence.lean` | D(t) -> 0 convergence theorem |
| `ContractionRate.lean` | Contraction rate gamma < 1 bound |
| `Lyapunov.lean` | Lyapunov function V(t) monotone decrease |
| `NonDegeneracy.lean` | Non-degeneracy via compactness + continuity |
| `SelfLimiting.lean` | Self-limiting contraction |
| `SelectivePersistence.lean` | Selective persistence of strong queries |
| `FanEffect.lean` | Fan effect: more queries -> slower learning |
| `ConvexHullInvariance.lean` | Weights stay in convex hull |
| `RetrievalInHull.lean` | Retrieved value in convex hull |
| `AttentionBudget.lean` | Attention budget conservation |
| `MonotoneAcquisition.lean` | Monotone score acquisition |
| `FiniteMemory.lean` | Finite memory capacity |
| `HistoryIndependence.lean` | History independence |
| `ContextVariation.lean` | Context variation bounds |
| `QueryNormBound.lean` | Query norm boundedness |
| `BlendRateBounds.lean` | Blend rate in (0,1) |
| `BoundedBias.lean` | Bounded bias |
| `RetrievalWeightBounds.lean` | Retrieval weight bounds |
| `RetrievalGatedStability.lean` | Retrieval-gated stability |
| `PrototypeFormation.lean` | Prototype formation |

### Rigidity (`Rigidity/`, 11 files)
Structural rigidity: why the loop's design is necessary.

| File | Key Theorems |
|------|-------------|
| `AccumulationRigidity.lean` | **Full rigidity trichotomy**: sublinear -> sigma dies, superlinear -> sigma blows up, sigma convergence -> sum_f = Theta(D^2) |
| `PipelineRigidity.lean` | 5-step pipeline is minimal; query formation invariant (iff characterization) |
| `CaptureRigidity.lean` | Capture step structure (permutation invariance, tight bounds) |
| `ConsolidationRigidity.lean` | Consolidation step structure |
| `ScoringAdditivity.lean` | Scoring rule invariance (additivity canonical but not forced) |
| `StepAblation.lean` | Each step is necessary (ablation) |
| `TargetAxioms.lean` | Target axiom independence |
| `CaptureScaleInvariant.lean` | Capture scale invariance |
| `IdempotentCapture.lean` | Idempotent capture |
| `RigiditySummary.lean` | Summary: forced/invariant/instance-defining trichotomy (query formation and scoring rule reclassified as invariant) |

### Sleep Dynamics (`Sleep/`, 18 files)
Sleep, dreaming, and wake-sleep cycle theorems.

| File | Key Theorems |
|------|-------------|
| `ForcedCycle.lean` | Forced sleep-wake oscillation |
| `DreamTransitions.lean` | Dream state transitions |
| `DreamAmnesia.lean` | Dream amnesia (spectral norm bound) |
| `SleepEfficacy.lean` | Sleep improves consolidation |
| `SleepDuration.lean` | Sleep duration bounds (actual log(V/delta)/gamma scaling) |
| `SleepGate.lean` | Sleep gating mechanism |
| `Wakeup.lean` | Wakeup conditions and attention fixed point |
| `Oscillation.lean` | Sleep-wake oscillation |
| `DebtObservable.lean` | Sleep debt is observable |
| `SelfObservable.lean` | Self-observable sleep pressure (gamma via contractionRate, joint rho < c AND gamma < eps condition) |
| `RetrievalDegradation.lean` | Retrieval degrades without sleep |
| `Maturation.lean` | Maturation effects |
| `SleepDebtThm.lean` | Sleep debt theorem |
| `MonotonePressure.lean` | Monotone sleep pressure |
| `Insomnia.lean` | Insomnia conditions |
| `Irreversibility.lean` | Irreversibility of consolidation |
| `ScoreBoost.lean` | Score boost from sleep |
| `SleepWakeCycle.lean` | Full sleep-wake cycle |

### Capture-Inertness (`CaptureInertness/`, 7 files)
Capture-consolidation cycle and inertness theorems.

| File | Key Theorems |
|------|-------------|
| `SigmaIncrement.lean` | Sigma increment and convergence |
| `SoftmaxLipschitz.lean` | Softmax Lipschitz bound (FTC + Jacobian norm) |
| `CaptureArgmax.lean` | Capture argmax properties |
| `FiniteArgmax.lean` | Finite argmax |
| `KZeroInertness.lean` | K=0 inertness |
| `PerturbativeInertness.lean` | Perturbative inertness |
| `ForcedCycleGeneralK.lean` | Forced cycle for general K |

### Appendix (`Appendix/`, 3 files)

| File | Key Theorems |
|------|-------------|
| `Naps.lean` | Nap duration and efficacy bounds |
| `SleepPhases.lean` | Sleep phase transitions (score spread + late uniform) |
| `SplitVsContinuous.lean` | Split vs continuous sleep (geometric decay) |

## Key Proof Highlights

### Accumulation Rigidity (the hardest proof)
The accumulation recurrence C(t+1) = C(t) + a(t)f(t)/C(t) with a(t) in [delta, 1] exhibits rigidity:

1. **Sublinear case** (`accum_sublinear_implies_sigma_zero`): If f = o(t), then sigma = C/(N0+t) -> 0. Uses a sigma-decrease argument: when sigma >= eps', the increment per step is at most eta/eps' (much less than 1), so D = N0+t outgrows C, forcing sigma below eps'. A barrier argument then preserves the bound.

2. **Main theorem** (`accumulation_rigidity_aggregate`): If sigma -> L > 0, then sum_{s<t} f(s) = Theta((N0+t)^2). The upper bound comes from C^2 >= 2*delta*sum_f and C <= 2*sigma*D. The lower bound requires `eventually_f_le_C_sq` (from sigma convergence, using eps = sigma*delta/10 and the algebraic inequality delta^2 - 22*delta + 80 > 0), then telescoping C^2 <= C(T0)^2 + 3*sum_f.

3. **Superlinear case** (`accum_superlinear_implies_sigma_unbounded`): If f(t) >= c*(t+1)^2, then sum_f >= c*t^3/4, so C^2 >= delta*c*t^3/2, giving C/D -> infinity.

**Note**: The pointwise statement f = Theta(t) is unprovable (counterexample: sparse spikes at powers of 2). The aggregate sum_f = Theta(D^2) is the correct formulation.

### Non-Degeneracy
Uses compactness of the bounded score set + continuity of the simplex map to show the infimum of attention weights is positive. Key Mathlib: `exists_mem_eq_inf'`, `isCompact_univ_pi`.

### Softmax Lipschitz
FTC-based proof: the Lipschitz constant equals the supremum of the Jacobian's operator norm. Uses `div_pow`, `sq_le_sq'`, and careful bounds on (a*f/C)^2.

## Build Instructions

```bash
cd SleepLoop
lake build          # Full build (~3183 jobs)
lake env lean SleepLoop/Rigidity/AccumulationRigidity.lean  # Single file
```

## Verification

```bash
# Check for sorries
grep -r "sorry" SleepLoop/SleepLoop/ --include="*.lean" | grep -v "^.*--"

# Count warnings
lake build 2>&1 | grep -c "warning:"
```

## History

| Session | Sorries | Key Work |
|---------|---------|----------|
| 1 | 178 -> ~120 | Initial structure, definitions, basic lemmas |
| 2 | ~120 -> ~60 | Core dynamics, Lyapunov, convergence infrastructure |
| 3 | ~60 -> ~30 | Sleep dynamics, capture-inertness, True placeholder audit |
| 4 | ~30 -> ~15 | SoftmaxLipschitz, NonDegeneracy, SigmaIncrement |
| 5 | ~15 -> 9 | CaptureRigidity, SplitVsContinuous, Naps, DreamTransitions |
| 6 | 9 -> **0** | AccumulationRigidity (full trichotomy), remaining sorries |
