/-
  SleepLoop/Verification.lean

  Axiom audit for the SleepLoop formalization.

  ## How to read the output

  Run: `lake env lean SleepLoop/Verification.lean`

  For each `#print axioms` command, Lean prints every axiom in the entire
  proof chain — transitively, through all imports and dependencies. If ANY
  declaration anywhere in the chain used `sorry`, you would see `sorryAx`
  in the list. If any custom `axiom` was declared, it would appear by name.

  **Expected output for every line:**

      'theoremName' depends on axioms: [propext, Classical.choice, Quot.sound]

  These three are the standard Lean axioms that every proof uses:
    - `propext`          — propositions with the same truth value are equal
    - `Classical.choice` — the axiom of choice (classical logic)
    - `Quot.sound`       — quotient soundness

  If you see ONLY these three for `mainTheorem`, it means:
    ✓ Zero `sorry` anywhere in the proof chain
    ✓ Zero custom `axiom` declarations
    ✓ Zero escape hatches of any kind
    ✓ The Lean kernel verified the entire proof from axioms to conclusion

  ## What `mainTheorem` covers

  `mainTheorem : StatementOfTheorem` is the conjunction of five properties
  stated in `MainTheorem.lean` using only Mathlib types (no project imports):
    1. Convergence: V(t) → 0 under repeated consolidation
    2. Accumulation rigidity: Σf = Θ(D²) when σ converges
    3. Sublinear → σ → 0
    4. Superlinear → σ → ∞
    5. Softmax Lipschitz: ‖φ(x) - φ(y)‖₁ ≤ 2‖x - y‖∞
-/
import SleepLoop.ProofOfMainTheorem

/-! ## Main theorem — the single check that covers everything -/

-- If this shows ONLY [propext, Classical.choice, Quot.sound],
-- the entire formalization is axiom-clean: no sorry, no custom axioms.
#print axioms mainTheorem

/-! ## Individual component theorems -/

-- Convergence (Corollary 17): D(t) → 0
#print axioms convergence_under_consolidation

-- Accumulation rigidity (Proposition 7): Σf = Θ(D²)
#print axioms accumulation_rigidity_aggregate

-- Sublinear ⟹ σ → 0
#print axioms accum_sublinear_implies_sigma_zero

-- Superlinear ⟹ σ → ∞
#print axioms accum_superlinear_implies_sigma_unbounded

-- Softmax Lipschitz (Lemma 81): ‖φ(x) - φ(y)‖₁ ≤ 2‖x - y‖∞
#print axioms softmax_lipschitz
