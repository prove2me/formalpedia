-- Prove2me | Theorems.Thm_efron_stein_increment_le
-- name    : efron_stein_increment_le
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T17:22:17.739027+00:00
-- url     : https://prove2.me/theorems/79f90908-66aa-4a19-a099-5b070263d3d9
-- statement:
--   Per-step Efron–Stein increment bound on a finite product probability space: the prefix-conditional expectation of the variance of E[Z | prefix of (insert i s)] is at most the integral over the cube of the coordinate-i variance of Z (resampling only coordinate i). The van Handel/BLM per-step martingale increment bound E[Delta_k^2] <= E[Var_k].
-- source:
--   van Handel, Probability in High Dimension (APC 550), Section 2.1, Theorem 2.3; Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Chapter 3, Theorem 3.1.

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem efron_stein_increment_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (i : ι) (hi : i ∉ s)
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    (Measure.pi μ)[Var[(Measure.pi μ)[Z | (Filtration.piFinset (X := α)) (insert i s)];
        Measure.pi μ | (Filtration.piFinset (X := α)) s]]
      ≤ ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) := by
  sorry
