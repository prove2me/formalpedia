-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_upper_tail_exact
-- name    : ReweightedNPMLE.gamma_upper_tail_exact
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:45:54.79241+00:00
-- url     : https://prove2.me/theorems/2316acca-422e-52ae-bb16-ba2dfc975886
-- title:
--   Optimized upper Chernoff bound for mean-one Gamma weights
-- statement:
--   If $a>0$ and $X\sim\operatorname{Gamma}(a,a)$, then for every $t\ge0$, $$\Pr(X\ge1+t)\le\exp\{-a[t-\log(1+t)]\}.$$ This exact rate-function estimate is the upper-tail input to the weight concentration event.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L433-L470

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

theorem ReweightedNPMLE.gamma_upper_tail_exact {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (gammaMeasure a a).real {x | 1 + t ≤ x} ≤
      Real.exp (-a * (t - Real.log (1 + t))) := by sorry
