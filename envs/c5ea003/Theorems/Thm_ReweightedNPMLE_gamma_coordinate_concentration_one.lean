-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_coordinate_concentration_one
-- name    : ReweightedNPMLE.gamma_coordinate_concentration_one
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:46:19.796372+00:00
-- url     : https://prove2.me/theorems/4887f540-27f1-440d-83cc-d24ed6d55454
-- title:
--   Two-sided Gamma concentration at the endpoint deviation
-- statement:
--   For $a>0$ and $X\sim\operatorname{Gamma}(a,a)$, $$\Pr(|X-1|>1)\le2e^{-a/4}.$$ This completes the coordinate bound at $t=1$, where the lower-tail logarithmic formula is unavailable.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L560-L593

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

theorem ReweightedNPMLE.gamma_coordinate_concentration_one {a : ℝ} (ha : 0 < a) :
    (gammaMeasure a a).real {x | |x - 1| > 1} ≤
      2 * Real.exp (-a / 4) := by sorry
