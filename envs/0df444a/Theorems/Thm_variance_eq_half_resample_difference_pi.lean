-- Prove2me | Theorems.Thm_variance_eq_half_resample_difference_pi
-- name    : variance_eq_half_resample_difference_pi
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T02:30:32.672757+00:00
-- url     : https://prove2.me/theorems/2e90cbf8-ef78-4447-9a1e-3d5af84212c6
-- statement:
--   **Global resampling (symmetrization) identity on a product cube.** For a square-integrable functional $Z \in L^2(\mu)$ of independent coordinates ($\mu = \bigotimes_i \mu_i$ a product of probability measures over a finite index set), the variance equals one half of the expected squared difference of $Z$ evaluated at two independent draws $\omega, \omega' \sim \mu$:
--
--   $$\operatorname{Var}(Z) = \tfrac12 \,\mathbb{E}_{\omega,\omega'}\big[(Z(\omega) - Z(\omega'))^2\big] = \tfrac12 \int (Z(\omega) - Z(\omega'))^2 \, d\mu(\omega)\,d\mu(\omega').$$
--
--   This is the resampling identity $\operatorname{Var}(W) = \tfrac12 \mathbb{E}[(W-W')^2]$ for an independent copy, instantiated on the product space $\mu \otimes \mu$ with $W(\omega,\omega') = Z(\omega)$ and $W'(\omega,\omega') = Z(\omega')$: these are independent (disjoint factors) and identically distributed (both are $Z$ pushed by the measure-preserving coordinate projections). It is the all-coordinates-at-once form of the Efron–Stein resampling principle; the per-coordinate refinement replaces the full independent copy $\omega'$ by a single-coordinate resample, yielding $\operatorname{Var}(Z) \le \tfrac12 \sum_i \mathbb{E}[(Z - Z'_i)^2]$.
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

theorem variance_eq_half_resample_difference_pi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    variance Z (Measure.pi μ)
      = (∫ p, (Z p.1 - Z p.2) ^ 2 ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by sorry
