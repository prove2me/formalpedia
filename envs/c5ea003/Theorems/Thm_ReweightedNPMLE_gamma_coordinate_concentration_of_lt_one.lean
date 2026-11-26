-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_coordinate_concentration_of_lt_one
-- name    : ReweightedNPMLE.gamma_coordinate_concentration_of_lt_one
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:46:11.30731+00:00
-- url     : https://prove2.me/theorems/cac4ee4c-7841-5f75-a418-8105068ca997
-- title:
--   Two-sided Gamma concentration for deviations below one
-- statement:
--   For $a>0$, $X\sim\operatorname{Gamma}(a,a)$, and $0<t<1$, $$\Pr(|X-1|>t)\le2e^{-at^2/4}.$$ The inequality controls a single random likelihood weight in the moderate-deviation range.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L522-L558

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

theorem ReweightedNPMLE.gamma_coordinate_concentration_of_lt_one {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t < 1) :
    (gammaMeasure a a).real {x | |x - 1| > t} ≤
      2 * Real.exp (-a * t ^ 2 / 4) := by sorry
