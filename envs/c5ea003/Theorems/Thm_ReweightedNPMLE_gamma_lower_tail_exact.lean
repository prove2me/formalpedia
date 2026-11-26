-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_lower_tail_exact
-- name    : ReweightedNPMLE.gamma_lower_tail_exact
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:53.048436+00:00
-- url     : https://prove2.me/theorems/8b68e19e-fc64-52a5-862f-985add3c4ea3
-- title:
--   Optimized lower Chernoff bound for mean-one Gamma weights
-- statement:
--   If $a>0$ and $X\sim\operatorname{Gamma}(a,a)$, then for $0\le t<1$, $$\Pr(X\le1-t)\le\exp\{-a[-t-\log(1-t)]\}.$$ This bound controls the lower tail while keeping the exact Gamma rate function.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L472-L512

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

theorem ReweightedNPMLE.gamma_lower_tail_exact {a t : ℝ} (ha : 0 < a) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    (gammaMeasure a a).real {x | x ≤ 1 - t} ≤
      Real.exp (-a * (-t - Real.log (1 - t))) := by sorry
