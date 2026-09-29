-- Prove2me | Theorems.Thm_resample_measure_preserving
-- name    : resample_measure_preserving
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T02:30:25.502859+00:00
-- url     : https://prove2.me/theorems/0e0ba837-0976-4e63-9037-f0fb0fbb2878
-- statement:
--   **The single-coordinate resample map is measure-preserving on a product cube.** Let $\mu = \bigotimes_i \mu_i$ be a product of probability measures on $\prod_i \alpha_i$ (finite index set), and fix a coordinate $i$. The map $(\omega, \omega') \mapsto \omega^{(i \leftarrow \omega'_i)}$, which replaces the $i$-th coordinate of $\omega$ by $\omega'_i$ (leaving the other coordinates of $\omega$ unchanged), pushes the product measure $\mu \otimes \mu$ forward to $\mu$. Equivalently: resampling one coordinate of a draw from a product measure, using an independent copy, leaves the distribution unchanged. This is the measure-theoretic backbone of the resampling form of the Efron–Stein inequality: it makes $Z(\omega)$ and $Z(\omega^{(i \leftarrow \omega'_i)})$ identically distributed, so the resampled difference $Z - Z'_i$ is well-behaved.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 Tensorization and bounded differences (Efron-Stein via the resampling / symmetrization identity Var(W)=½E[(W-W')^2] for an independent copy); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3, Theorem 3.1 (the resampling form of the Efron-Stein inequality on a product space).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem resample_measure_preserving
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun p : (∀ j, α j) × (∀ j, α j) => Function.update p.1 i (p.2 i))
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by sorry
