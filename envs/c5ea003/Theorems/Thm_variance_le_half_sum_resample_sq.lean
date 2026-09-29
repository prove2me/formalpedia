-- Prove2me | Theorems.Thm_variance_le_half_sum_resample_sq
-- name    : variance_le_half_sum_resample_sq
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T17:28:10.864063+00:00
-- url     : https://prove2.me/theorems/3cde2bd7-a9e7-4e3a-bd6c-cc80cd435042
-- statement:
--   Efron–Stein resampling inequality: Var(Z) <= (1/2) * sum over coordinates i of E_{omega,omega'}[(Z(omega) - Z(update omega i (omega' i)))^2], with omega, omega' two independent product-measure draws and the i-th coordinate of omega resampled from omega'.
-- source:
--   van Handel, Probability in High Dimension (APC 550), Section 2.1, Theorem 2.3; Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Chapter 3, Theorem 3.1.

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem variance_le_half_sum_resample_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    variance Z (Measure.pi μ)
      ≤ (∑ i, ∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
            ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by
  sorry
