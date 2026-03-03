/-
  SleepLoop/Defs/Scoring.lean

  Definition: Perturbed score S'(tau) = S(tau) + sigma(tau) + b(tau),
  and the admissible scoring rule structure.
  Paper: Definition 1 (def:scoring), §2.1;
         Definition 17 (def:admissible_scoring), §2.3.
-/
import SleepLoop.Defs.SimplexMap
import SleepLoop.Defs.LoopState

/-! ## Scoring -/

/-- The perturbed score: S'(τ) = S(τ) + σ(τ) + b(τ).
    Paper: Definition 1 (def:scoring). -/
noncomputable def perturbedScore {X : Type*} [Fintype X]
    (S σ b : X → ℝ) (τ : X) : ℝ :=
  S τ + σ τ + b τ

/-- An admissible scoring rule h : ℝ³ → ℝ.
    Paper: Definition 17 (def:admissible_scoring).
    (W1) C¹, (W2) depends on σ and b, (W3) non-degenerate in s. -/
structure AdmissibleScoringRule where
  h : ℝ → ℝ → ℝ → ℝ
  smooth : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2)
  -- (W2) and (W3) are hard to state generically; we axiomatize them
  nondegen_sigma : ∃ σ₁ σ₂ b, h 0 σ₁ b ≠ h 0 σ₂ b
  nondegen_bias : ∃ σ b₁ b₂, h 0 σ b₁ ≠ h 0 σ b₂
  faithful : ∃ s₁ s₂, h s₁ 0 0 ≠ h s₂ 0 0

/-- The canonical additive scoring rule: h(s,σ,b) = s + σ + b.
    Paper: Proposition 18 (prop:scoring_additivity). -/
noncomputable def additiveScoring : AdmissibleScoringRule where
  h := fun s σ b => s + σ + b
  smooth := by
    show ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ => p.1 + p.2.1 + p.2.2)
    exact (contDiff_fst.add (contDiff_fst.comp contDiff_snd)).add
      (contDiff_snd.comp contDiff_snd)
  nondegen_sigma := ⟨0, 1, 0, by norm_num⟩
  nondegen_bias := ⟨0, 0, 1, by norm_num⟩
  faithful := ⟨0, 1, by norm_num⟩
