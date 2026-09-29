-- Prove2me | Theorems.Thm_variance_le_sum_expected_condVarCoord
-- name    : variance_le_sum_expected_condVarCoord
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T17:26:40.399124+00:00
-- url     : https://prove2.me/theorems/864ea70e-9360-4c25-a994-6d30c03c7f2e
-- statement:
--   Efron–Stein tensorization of variance on a finite product probability space: Var(Z) is at most the sum over coordinates i of the integral over the cube of the coordinate-i variance of Z (the variance taken by resampling only the i-th coordinate).
-- source:
--   van Handel, Probability in High Dimension (APC 550), Section 2.1, Theorem 2.3; Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Chapter 3, Theorem 3.1.

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem variance_le_sum_expected_condVarCoord
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    variance Z (Measure.pi μ)
      ≤ ∑ i, ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) := by
  sorry
