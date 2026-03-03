# Verification Guide

How to verify the SleepLoop formalization without reading 10,000 lines of Lean.

## Quick version (5 minutes, any platform)

```bash
# 1. Read the theorem statement (one file, Mathlib-only types)
cat SleepLoop/MainTheorem.lean

# 2. Confirm it imports only Mathlib
grep "^import" SleepLoop/MainTheorem.lean
# Should show only "import Mathlib.*" lines. No "import SleepLoop.*".

# 3. Build and verify axioms
lake build
lake env lean SleepLoop/Verification.lean
# Should print: 'mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That's it. If step 1 shows non-trivial mathematics, step 2 confirms no project
contamination, and step 3 shows only standard axioms, then Lean's kernel has
verified the entire proof chain from Mathlib-only statement through all 80 files.

## Verification tiers

### Tier 1: Standard (any platform)

Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) via elan,
then:

```bash
lake build                              # build all 3183 jobs
lake env lean SleepLoop/Verification.lean  # check axioms
./scripts/validate.sh                   # full automated pipeline (checks 1-6)
```

This covers: build, sorry check, custom axiom check, True placeholder check,
axiom dependencies, and MainTheorem import isolation.

### Tier 2: lean4checker (any platform)

[lean4checker](https://github.com/leanprover/lean4checker) replays every
declaration through a fresh Lean kernel, detecting any environment hacking.

```bash
# Install (one-time)
git clone https://github.com/leanprover/lean4checker
cd lean4checker && git checkout v4.28.0 && lake build && cd ..

# Run (after lake build)
lake env ../lean4checker/.lake/build/bin/lean4checker
```

If this passes, you are trusting only the Lean kernel implementation
(~10K lines of C++) and nothing else.

### Tier 3: Comparator (Linux/WSL only)

[Comparator](https://github.com/leanprover/comparator) is leanprover's
trustworthy proof judge. It treats the proof files as untrusted, builds them
in a [landrun](https://github.com/Zouuup/landrun) sandbox, and independently
verifies that `ProofOfMainTheorem.lean` proves the exact same statement as
`MainTheorem.lean` using only permitted axioms.

**Requires Linux** (native or WSL). Landrun uses Linux landlock for sandboxing.

```bash
# Install dependencies (one-time)
# 1. landrun: https://github.com/Zouuup/landrun (requires Linux kernel >= 5.13)
# 2. lean4export: https://github.com/leanprover/lean4export (match Lean version)
# 3. comparator:
git clone https://github.com/leanprover/comparator
cd comparator && lake build && cd ..

# Run (after lake build)
lake env ../comparator/.lake/build/bin/comparator comparator.json
```

The config (`comparator.json`) is already set up:
- Challenge: `SleepLoop.MainTheorem` (Mathlib-only statement)
- Solution: `SleepLoop.ProofOfMainTheorem` (proof)
- Theorem: `mainTheorem`
- Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`

### Tier 4: Docker (full from-scratch, any platform)

Builds everything from scratch in an isolated container,
including lean4checker and comparator. Nothing to install locally except an OCI
runtime (Docker, Podman, etc.).

```bash
docker build -t sleeploop-verify .
docker run --rm sleeploop-verify
```

For an interactive shell:
```bash
docker run --rm -it sleeploop-verify bash
```

**Note:** The Docker build takes 10-20 minutes (downloads Lean, Mathlib, builds
everything from source, installs all verification tools).

Comparator (step 8) requires Linux landlock, which is unavailable inside
Docker Desktop (Windows/macOS). It will show SKIP. This is expected.
All other checks (1-7) still run, including lean4checker which independently
replays every declaration through a fresh kernel. For full comparator
verification, use Tier 3 on native Linux or WSL.

Any OCI-compatible runtime works. Docker Engine (Linux), Podman (all platforms,
daemonless), or Docker Desktop (Windows/macOS, needs ~8GB RAM).

## Expected output

Running `./scripts/validate.sh` on a passing build produces:

```
=== SleepLoop Validation ===

[1] Building...
  PASS: Build succeeded (287s)
[2] Checking for sorry...
  PASS: No sorry found
[3] Checking for custom axioms...
  PASS: No custom axioms
[4] Checking for True placeholders...
  PASS: No True placeholders
[5] Verifying axiom dependencies...
  'mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
  'convergence_under_consolidation' depends on axioms: [propext, Classical.choice, Quot.sound]
  'accumulation_rigidity_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound]
  'accum_sublinear_implies_sigma_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
  'accum_superlinear_implies_sigma_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
  'softmax_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
  PASS: mainTheorem uses only standard axioms
[6] Auditing MainTheorem.lean imports...
  PASS: MainTheorem.lean imports only Mathlib
[7] Running lean4checker...
  PASS: lean4checker verified all declarations
[8] Running comparator...
  PASS: comparator verified proof matches statement

=== Stats ===
  Lean files: 80
  Lines of code: ~11500

=== ALL CHECKS PASSED: 8 passed, 0 failed (312s) ===
```

Steps 7-8 show SKIP instead of PASS if lean4checker/comparator are not installed.
Step 8 shows SKIP inside Docker Desktop (Windows/macOS) because landlock is
unavailable in the VM. On native Linux with kernel >= 5.13, all 8 checks pass.

## Trust model

The kernel (type checker, ~10K lines of C++) is the only trusted component.
The 80 project files are verified by the kernel.

You only need to verify that the statement in `MainTheorem.lean` says what
you think it says. That file uses only Mathlib types with no project imports,
so there is no way to hide triviality behind a custom definition.

`#print axioms` shows only `[propext, Classical.choice, Quot.sound]`,
the three standard axioms present in every Lean proof. Any `sorry` would
appear as `sorryAx`; any custom axiom would be listed explicitly.
`lean4checker` replays all declarations through a fresh kernel, guarding
against environment manipulation via metaprogramming.

## Full automated validation

```bash
./scripts/validate.sh
```

This checks:
1. Full build (0 errors)
2. No `sorry` in any `.lean` file
3. No custom `axiom` declarations
4. No `True` placeholder statements
5. `#print axioms mainTheorem` shows only standard axioms
6. `MainTheorem.lean` has no project imports
7. lean4checker kernel replay (if installed)
8. Comparator sandboxed verification (if installed, Linux only)

## Inspection report (for Lean reviewers)

To see the full dependency and structure breakdown (Mathlib imports, proof
techniques, declaration counts):

```bash
./scripts/inspect.sh
```

This extracts everything automatically from the source files: which Mathlib
modules are imported, which files use compactness / FTC / convexity / convergence
arguments, theorem/lemma counts, and confirms the MainTheorem isolation.

## File-by-file audit path

If you want to go deeper than the quick version:

1. **`SleepLoop/MainTheorem.lean`**. Read the five property statements.
   Confirm they are mathematically non-trivial. No project imports.

2. **`SleepLoop/ProofOfMainTheorem.lean`**. The bridge file.
   Imports MainTheorem + project files and proves `mainTheorem :
   StatementOfTheorem`. Constructs project types from inline types
   and shows the definitions match.

3. **`SleepLoop/Verification.lean`**. Runs `#print axioms` on the
   main theorem and five key component theorems.

4. **Individual proof files**. Doc comments in each file explain
   the proof strategy and cite the paper.

## Troubleshooting

**Build is slow on first run**
The first `lake build` fetches and compiles Mathlib dependencies (~3000 jobs,
10-20 minutes). Subsequent builds are incremental and fast. The Docker build
fetches the Mathlib cache to speed this up.

**Network errors during build**
`lake exe cache get` downloads pre-built Mathlib `.olean` files. If this fails
(firewall, no internet), the build will compile Mathlib from source instead —
slower but still works.

**Docker build runs out of memory**
Lean builds need ~8GB RAM. If Docker is configured with less (common on
Docker Desktop), increase it in Docker Desktop settings or use `--memory=8g`.

**Windows line ending issues**
If you see unexpected build errors on Windows, ensure git didn't convert line
endings: `git config core.autocrlf input` and re-clone.

**`lake build` hangs or shows no output**
Lean's build system prints progress as jobs complete. The first few minutes
may show no output while Mathlib dependencies are resolved. This is normal.

## Reproducibility

The build is fully reproducible:
- `lean-toolchain`: Lean 4.28.0
- `lake-manifest.json`: pins exact Mathlib commit
- Same toolchain + manifest = identical `.olean` files

To reproduce from scratch:
```bash
git clone https://github.com/nemustudies/sleep-loop
cd sleep-loop
lake build    # fetches Mathlib, builds everything
```
