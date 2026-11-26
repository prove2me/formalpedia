-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianReal_two_sided_tail
-- name    : ReweightedNPMLE.gaussianReal_two_sided_tail
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:43:50.417825+00:00
-- url     : https://prove2.me/theorems/887d9593-2ddd-42eb-a766-7f2b1382b717
-- title:
--   Two-sided Chernoff bound for a standard Gaussian
-- statement:
--   For a standard normal variable $Z\sim N(0,1)$ and every $t>0$, $$\Pr(|Z|>t)\le2e^{-t^2/2}.$$ This one-dimensional bound is the starting point for sample-radius control in Gaussian location mixtures.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianRadius.lean#L18-L79

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

open ReweightedNPMLE

theorem ReweightedNPMLE.gaussianReal_two_sided_tail {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real {x : ℝ | |x| > t} ≤
      2 * Real.exp (-t ^ 2 / 2) := by sorry
