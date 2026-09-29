-- Prove2me | solution 1 for SCAFFOLD.FiniteRoundConvergence
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-24T04:36:27.327966+00:00
-- url     : https://prove2.me/submissions/69509257-d50e-4948-8e41-5500dc86a2da

import Theorems.Thm_SCAFFOLD_ConvexFiniteRoundConvergence
import Theorems.Thm_SCAFFOLD_NonconvexFiniteRoundConvergence

open MeasureTheory SCAFFOLD
universe u
set_option autoImplicit false

/-- The two convergence regimes are the existing mission milestones. -/
theorem solution :
(
  ∀ (d N : ℕ) (P : Problem d N) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (S K T : ℕ) (ηl ηg μ : ℝ) (c0 : Fin N → Space d) (xstar : Space d),
    Convexity P μ → IsMinimizer P xstar → 0 < ηl → 1 ≤ ηg →
    effectiveStep K ηl ηg ≤ 1 / (81 * P.β) →
    μ * effectiveStep K ηl ηg ≤ (S : ℝ) / (15 * (N : ℝ)) →
    ∀ A : Run P ν S K T ηl ηg (some c0),
      weightedGap A xstar μ ≤ convexRHS P S K T ηl ηg μ c0 xstar
) ∧ (
  ∀ (d N : ℕ) (P : Problem d N) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (S K T : ℕ) (ηl ηg fLower : ℝ),
    (∀ x, fLower ≤ objective P.f x) → 0 < ηl → 1 ≤ ηg →
    effectiveStep K ηl ηg ≤
      Real.rpow ((S : ℝ) / (N : ℝ)) (2 / 3 : ℝ) / (24 * P.β) →
    ∀ A : Run P ν S K T ηl ηg none,
      averageGradientSq A ≤ nonconvexRHS P S K T ηl ηg fLower
) := by
  exact ⟨SCAFFOLD.ConvexFiniteRoundConvergence,
    SCAFFOLD.NonconvexFiniteRoundConvergence⟩
