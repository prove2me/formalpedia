-- Prove2me | solution 1 for variance_le_half_sum_resample_sq
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T17:28:13.813518+00:00
-- url     : https://prove2.me/submissions/a10afc4b-2ab3-40d3-9796-5c137d0b9899

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_variance_le_sum_expected_condVarCoord
import Theorems.Thm_expected_condVar_coord_eq_half_resample

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

/-- **Efron–Stein resampling inequality on a finite product probability space.**
`Var(Z) ≤ ½ ∑ᵢ E_{ω,ω'}[(Z ω − Z(update ω i (ω' i)))²]`, where `ω, ω'` are two
independent draws from the product measure and the `i`-th coordinate of `ω` is
resampled from `ω'`.  This is BLM Ch.3 Theorem 3.1 (the resampling form of
Efron–Stein), obtained from the tensorization bound `Var(Z) ≤ ∑ᵢ E[Var_i Z]` by
rewriting each per-coordinate conditional variance as half the expected squared
resampling difference.
Source: van Handel, Probability in High Dimension (APC 550), §2.1; Boucheron–
Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 3, Theorem 3.1. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    variance Z (Measure.pi μ)
      ≤ (∑ i, ∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
            ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by
  classical
  have htens := variance_le_sum_expected_condVarCoord (μ := μ) hZ
  -- rewrite each per-coordinate conditional-variance term via the per-coord identity
  have hterm : ∀ i : ι,
      (∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ))
        = (∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
            ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by
    intro i
    exact expected_condVar_coord_eq_half_resample (μ := μ) i hZ
  have hsum :
      (∑ i, ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ))
        = (∑ i, ∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
              ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  rw [hsum] at htens
  exact htens
