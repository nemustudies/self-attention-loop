# a math loop that sleeps and dreams

A self-referring attention loop operating on finite memory through five steps
(observe, accumulate, retrieve, consolidate, capture), governed by a
three-level hierarchy of simplex maps. Five definitions produce the entire
loop. 103 properties follow inevitably. The loop must sleep or permanently
degenerate.

## What's here

| | |
|---|---|
| [`a_math_loop_that_sleeps_and_dreams.pdf`](a_math_loop_that_sleeps_and_dreams.pdf) | The paper |
| [`SleepLoop/`](SleepLoop/) | Lean 4 formalization (0 sorries, 80 files, ~11,500 lines) |
| [`blueprint.html`](blueprint.html) | Interactive proof architecture |
| [`sleep_loop_implementation.py`](sleep_loop_implementation.py) | PyTorch implementation |
| [`proof_dependency_graph.png`](proof_dependency_graph.png) | Proof dependency visualization |
| [`VERIFICATION_GUIDE.md`](VERIFICATION_GUIDE.md) | How to verify the proofs |
| [`Dockerfile`](Dockerfile) | Reproducible verification container |

> **Reviewers: start here.** See [`VERIFICATION_GUIDE.md`](VERIFICATION_GUIDE.md)
> for a step-by-step walkthrough. The short version: read
> [`SleepLoop/MainTheorem.lean`](SleepLoop/MainTheorem.lean) (Mathlib-only
> statement, no project imports), then run
> `lake env lean SleepLoop/Verification.lean` to confirm only standard axioms.

## Formalization

## Status

| Metric | Value |
|--------|-------|
| Sorries | **0** |
| Axioms | **0** (no `axiom` beyond Lean/Mathlib) |
| Build jobs | 3,183 |
| Lean files | 80 |
| Lines of code | ~11,500 |
| Lean version | 4.28.0 |
| Mathlib version | v4.28.0 |

## Setup

```bash
./scripts/setup.sh          # Lean only (elan + lean4)
./scripts/setup.sh --full   # + numpy, torch, lean4checker
```

Or install manually: [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
via elan, then `lake build` (fetches Mathlib on first build).

## Build Instructions

```bash
cd SleepLoop
lake build          # Full build (~3183 jobs, takes several minutes)
```

To check a single file:

```bash
lake env lean SleepLoop/Rigidity/AccumulationRigidity.lean
```

## Module Structure

| Directory | Files | Description |
|-----------|------:|-------------|
| `Defs/` | 13 | Core definitions: simplex maps, loop state, five-step operations, derived quantities |
| `Core/` | 24 | Main dynamics: convergence, Lyapunov, contraction rate, non-degeneracy, forgetting curve, spacing effect, testing effect, retrieval crossover |
| `Rigidity/` | 10 | Structural rigidity: why each design choice is forced or invariant |
| `Sleep/` | 18 | Sleep dynamics: efficacy, debt, dreaming, oscillation, wakeup |
| `CaptureInertness/` | 7 | Capture-consolidation cycle: sigma convergence, softmax Lipschitz, inertness |
| `Appendix/` | 3 | Extensions: naps, sleep phases, split vs. continuous sleep |

Plus `SleepLoop.lean` (root import file) for 80 total.

## Paper-to-Lean Mapping

### Definitions (Defs/)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| -- | -- | `Defs/SimplexMap.lean` | Three-level simplex map hierarchy: A, A+, softmax |
| -- | -- | `Defs/BlendRate.lean` | Admissible blend rate class L |
| -- | -- | `Defs/Embedding.lean` | Embedding E : X -> R^d with radius R |
| -- | -- | `Defs/LoopState.lean` | Full loop state: M, C, N, t |
| def:scoring | 1 | `Defs/Scoring.lean` | Perturbed score S'(tau) = S + sigma + b |
| def:observation | 2 | `Defs/Observation.lean` | Step 1: a = phi(S') |
| def:accumulation | 3 | `Defs/Accumulation.lean` | Step 2: C(t+1) = C(t) + a(t) f(t) / C(t) |
| def:retrieval | 4 | `Defs/Retrieval.lean` | Step 3: q = aE, w = phi(qM^T), l = wM, b = EKl |
| def:consolidation | 5 | `Defs/Consolidation.lean` | Step 4: blend toward T_j |
| def:capture | 6 | `Defs/Capture.lean` | Step 5: M' = M union {E(tau) : q.E(tau) > theta} |
| -- | -- | `Defs/DerivedQuantities.lean` | V, D, rho, gamma, g, R, critical memory size |
| def:cluster | 14-17 | `Defs/Cluster.lean` | Epsilon-clusters, cluster salience, inter-cluster separation |
| def:sleep_debt | 18-19 | `Defs/SleepDebt.lean` | Sleep debt, inter-episode transitions, naps |

### Rigidity (Paper Section 2)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| prop:consolidation_rigidity | 1 | `Rigidity/ConsolidationRigidity.lean` | Forced boundary conditions lambda(0)=1, lambda(1)=0 |
| prop:rigidity | 3 | `Rigidity/AccumulationRigidity.lean` | Rigidity trichotomy: sublinear/linear/superlinear accumulation |
| lem:idempotent | 4 | `Rigidity/IdempotentCapture.lean` | Capture is idempotent |
| cor:capture_scale_invariant | 4 | `Rigidity/CaptureScaleInvariant.lean` | Capture decision is scale-invariant in q |
| prop:capture_rigidity | 5 | `Rigidity/CaptureRigidity.lean` | Max threshold is unique under idempotent capture |
| prop:target_axioms | 6 | `Rigidity/TargetAxioms.lean` | Minimal axioms (T1-T5) for consolidation target |
| prop:pipeline_rigidity | 7 | `Rigidity/PipelineRigidity.lean` | 5-step pipeline is minimal; query formation invariant (iff), dot-product scoring forced |
| prop:scoring_additivity | 9 | `Rigidity/ScoringAdditivity.lean` | Additive scoring is canonical under softmax factorization |
| prop:step_ablation | 10 | `Rigidity/StepAblation.lean` | Each of the 5 steps is necessary |
| rem:rigidity_summary | -- | `Rigidity/RigiditySummary.lean` | Summary: forced/invariant/instance-defining trichotomy (query formation and scoring rule reclassified as invariant) |

### Core Dynamics (Paper Section 3)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| cor:N_history_independent | 1 | `Core/HistoryIndependence.lean` | N(t) = N(0) + t, independent of attention history |
| thm:selective | 2 | `Core/SelectivePersistence.lean` | Selective persistence: sigma -> 0 or liminf >= sqrt(delta) |
| lem:stability | 3 | `Core/RetrievalGatedStability.lean` | Anchor unchanged by consolidation, threshold non-decreasing |
| cor:acquisition | 4 | `Core/MonotoneAcquisition.lean` | \|M\| non-decreasing after capture |
| lem:hull | 5 | `Core/ConvexHullInvariance.lean` | conv(M_t) subset conv(E(X)) for all t |
| lem:finite | 6 | `Core/FiniteMemory.lean` | Without consolidation, \|M\| <= \|X\| |
| cor:bounded | 7 | `Core/BoundedBias.lean` | \|b(tau)\| <= R^2 \|\|K\|\|\_op |
| thm:nondegen | 8 | `Core/NonDegeneracy.lean` | Non-degeneracy: a(tau) >= alpha > 0 under A+ |
| cor:retrieval_in_hull | 9 | `Core/RetrievalInHull.lean` | l = wM lies in conv(M) |
| cor:query_norm_bound | 10 | `Core/QueryNormBound.lean` | \|\|q\|\| <= R and q in conv(E(X)) |
| cor:blend_rate_bounds | 11 | `Core/BlendRateBounds.lean` | lambda_v = 0, 0 < lambda_j <= 1 for j != v |
| lem:lyapunov | 12 | `Core/Lyapunov.lean` | V(t+1) < V(t) whenever V(t) > 0 |
| cor:budget | 13 | `Core/AttentionBudget.lean` | sum a(tau) = 1, mean = 1/n |
| cor:contraction | 14 | `Core/ContractionRate.lean` | V(t+1) <= (1 - gamma) V(t) |
| cor:fan | 15 | `Core/FanEffect.lean` | Adding impressions dilutes retrieval weights |
| cor:opposition | 16 | `Core/RetrievalWeightBounds.lean` | 1/n <= max w_j <= 1/(1+(n-1)exp(-g)) |
| cor:sleep | 17 | `Core/Convergence.lean` | D(t) -> 0 under repeated consolidation |
| cor:selflimiting | 18 | `Core/SelfLimiting.lean` | gamma(t) -> 0 as M converges |
| cor:prototype | 19 | `Core/PrototypeFormation.lean` | All rows of M converge to anchor v |
| cor:variability | 20 | `Core/ContextVariation.lean` | Anchor rotation preserves distinct impressions |
| cor:decay | -- | `Core/ForgettingCurve.lean` | Hyperbolic decay: sigma = C_T/(N_0 + t) when attention ceases |
| cor:testing | -- | `Core/TestingEffect.lean` | Testing effect: retrieval preserves anchor, displaces competitors |
| prop:spacing | -- | `Core/SpacingEffect.lean` | Spacing effect: inverted-U with K* = R/(n-1) |
| cor:crossover | -- | `Core/RetrievalCrossover.lean` | Retrieval advantage grows with delay (crossover effect) |

### Sleep Dynamics (Paper Section 4)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| thm:sleep_efficacy | 8 | `Sleep/SleepEfficacy.lean` | Sleep restores retrieval: V -> 0, D -> 0 under S=0 |
| thm:wakeup | 10 | `Sleep/Wakeup.lean` | Quasi-fixed-point under S=0 (6 parts) |
| prop:sleep_gate | 11 | `Sleep/SleepGate.lean` | S is external; loop cannot self-initiate sleep |
| cor:sleep_wake_cycle | 2 | `Sleep/SleepWakeCycle.lean` | (rho, gamma) defines complete sleep-wake control; joint condition rho < c AND gamma < eps |
| cor:sleep_duration | 3 | `Sleep/SleepDuration.lean` | T = sum T_k = O(log(V/delta)/gamma); proves actual log/gamma bound |
| thm:sleep_pressure | 39 | `Sleep/RetrievalDegradation.lean` | Retrieval precision degrades as \|M\| grows |
| thm:monotone_pressure | 42 | `Sleep/MonotonePressure.lean` | Sleep pressure is monotone during waking |
| cor:irreversible | 43 | `Sleep/Irreversibility.lean` | Waking cannot restore retrieval precision |
| thm:self_observable | 45 | `Sleep/SelfObservable.lean` | Sleep need detectable from (rho, gamma, mu); gamma uses contractionRate |
| thm:oscillation | 50 | `Sleep/Oscillation.lean` | Oscillatory gamma during multi-cluster sleep |
| thm:sleep_debt | 56 | `Sleep/SleepDebtThm.lean` | Sleep debt compounds, has threshold, recovers |
| cor:debt_observable | 58 | `Sleep/DebtObservable.lean` | Sleep debt is self-observable |
| thm:score_boost | 59 | `Sleep/ScoreBoost.lean` | Observation sharpening is retrieval-irrelevant |
| thm:dream_transitions | 62 | `Sleep/DreamTransitions.lean` | Inter-episode cross-cluster retrieval |
| thm:dream_amnesia | 65 | `Sleep/DreamAmnesia.lean` | Dream content is not stored |
| cor:maturation | 74 | `Sleep/Maturation.lean` | Sleep need declines with memory maturation |
| cor:forced_cycle | 76 | `Sleep/ForcedCycle.lean` | Forced quasi-periodic sleep-wake cycle |
| cor:insomnia | 79 | `Sleep/Insomnia.lean` | Cost of ignoring the sleep signal |

### Capture-Consolidation Cycle (Paper Section 5)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| thm:capture_argmax | 19 | `CaptureInertness/CaptureArgmax.lean` | Total captures <= argmax transitions + 1 |
| prop:capture_inertness | 20 | `CaptureInertness/PerturbativeInertness.lean` | Perturbative inertness for small \|\|K\|\| |
| cor:K_zero_inertness | 21 | `CaptureInertness/KZeroInertness.lean` | K=0 implies finite captures |
| cor:forced_cycle_general_K | 22 | `CaptureInertness/ForcedCycleGeneralK.lean` | Forced cycle for arbitrary K |
| lem:softmax_lipschitz | A.5 | `CaptureInertness/SoftmaxLipschitz.lean` | \|\|phi(x) - phi(y)\|\|\_1 <= 2\|\|x - y\|\|\_inf |
| lem:sigma_increment | A.6 | `CaptureInertness/SigmaIncrement.lean` | \|sigma(t+1) - sigma(t)\| = O(1/t) |
| lem:finite_argmax | A.7 | `CaptureInertness/FiniteArgmax.lean` | E-argmax stabilizes after finitely many transitions |

### Appendix

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| thm:sleep_phases | 84 | `Appendix/SleepPhases.lean` | Phase structure of S=0 regime |
| thm:nap | 90 | `Appendix/Naps.lean` | Naps as partial-cycle consolidation |
| cor:split_vs_continuous | 92 | `Appendix/SplitVsContinuous.lean` | Continuous vs. split sleep trade-off |

## Simplex Map Hierarchy

The paper's theorems are stratified by which level of simplex map they require:

- **A** (broadest): any map sending R^n to the probability simplex (nonneg,
  sum-to-one). Covers accumulation rigidity, convex hull invariance, step
  ablation, history independence, bounded bias, monotone acquisition.
- **A+** (positive, order-preserving, continuous): all outputs strictly
  positive, ordering preserved. Covers non-degeneracy, Lyapunov strict
  decrease, convergence, contraction rate, blend rate bounds, sleep efficacy.
- **softmax** (most restrictive): phi(x)\_i = exp(x\_i) / sum exp(x\_j).
  Covers fan effect, retrieval weight bounds, scoring additivity,
  capture-inertness, sleep pressure, monotone pressure, forced cycle.

Each theorem's doc comment in the Lean source indicates its required level.

## Key Theorems

**Accumulation Rigidity** (`Rigidity/AccumulationRigidity.lean`).
The hardest proof in the formalization. Establishes a trichotomy for the
generalized accumulation rule C(t+1) = C(t) + a(t) f(t) / C(t): if f is
sublinear then sigma -> 0; if f is superlinear then sigma -> infinity; and if
sigma converges to a positive constant then sum f = Theta(D^2). The aggregate
formulation is essential. The pointwise statement f = Theta(t) is unprovable
(counterexample: sparse spikes at powers of 2).

**Convergence** (`Core/Convergence.lean`).
The central convergence theorem: under repeated fixed-query consolidation with
A+, the diameter D(t) -> 0 and all impressions converge to the anchor. Built on
the Lyapunov strict decrease lemma and compactness of the convex hull.

**Sleep Efficacy** (`Sleep/SleepEfficacy.lean`).
Sleep restores retrieval precision: under S=0 with capture disabled,
V(t) strictly decreases, prototypes form via Cauchy-Schwarz, and the
contraction rate gamma -> 0 provides a natural termination signal.

**Non-Degeneracy** (`Core/NonDegeneracy.lean`).
Uses compactness of bounded score sets and continuity of A+ maps to prove a
uniform positive lower bound on attention: a(tau) >= alpha > 0 for all tau, t.
Key Mathlib ingredients: `isCompact_univ_pi` and `exists_mem_eq_inf'`.

**Softmax Lipschitz** (`CaptureInertness/SoftmaxLipschitz.lean`).
FTC-based proof that the softmax map is Lipschitz in the L1-to-Linf sense:
||phi(x) - phi(y)||\_1 <= 2 ||x - y||\_inf, via integration of the Jacobian
operator norm bound.

## Verification

CI runs automatically on every push and pull request. The pipeline checks:

1. Full build (0 errors)
2. No `sorry` in any proof file
3. No custom `axiom` declarations
4. No `True` placeholder statements
5. `#print axioms mainTheorem` shows only standard Lean axioms
6. `MainTheorem.lean` imports only Mathlib (no project dependencies)
7. **lean4checker** replays all declarations through a fresh kernel

Run locally with `./scripts/validate.sh` (step 7 requires
[lean4checker](https://github.com/leanprover/lean4checker)).
**comparator** verification requires Linux landlock; use the Dockerfile.
See [`VERIFICATION_GUIDE.md`](VERIFICATION_GUIDE.md) for details.

### Manual verification

To inspect the main theorem statement (Mathlib-only, no project types):

```bash
cat SleepLoop/MainTheorem.lean
```

To verify axiom dependencies:

```bash
lake env lean SleepLoop/Verification.lean
```

### Main theorem

`SleepLoop/MainTheorem.lean` states five key properties using only Mathlib types
(no project imports). `SleepLoop/ProofOfMainTheorem.lean` proves
`mainTheorem : StatementOfTheorem` by connecting inline definitions to the
project's existing theorems. `SleepLoop/Verification.lean` runs `#print axioms`
to confirm only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`)
appear in the proof chain.

### Docker

```bash
docker build -t sleeploop-verify .
docker run --rm sleeploop-verify
```

Runs all checks in an isolated container. Comparator may show SKIP on
Docker Desktop (Windows/macOS) because landlock is unavailable in the VM.
All other checks still run.

## Blueprint

An interactive proof blueprint is available at [`docs/index.html`](docs/index.html)
(or [online](https://nemu-sleeploop.github.io/SleepLoop/) once deployed).
Each theorem links to its Lean 4 source and shows its dependencies.

To rebuild locally:

```bash
pip install leanblueprint
bash scripts/build_blueprint.sh
```
### ai tool disclosure
llms were used in the development and writing of this paper

## Paper Reference

> nemu, "A Math Loop That Sleeps and Dreams," 2026.

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
