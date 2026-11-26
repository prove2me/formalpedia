-- Prove2me | Theorems.Thm_ReweightedNPMLE_centered_gamma_mgf
-- name    : ReweightedNPMLE.centered_gamma_mgf
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:52.246114+00:00
-- url     : https://prove2.me/theorems/d9d9658a-c42d-4e07-8a46-3d9eabfce4ba
-- title:
--   Exact moment-generating function of a centered mean-one Gamma variable
-- statement:
--   Let $a>0$, $X\sim\operatorname{Gamma}(a,a)$, and $t<a$. Then $$\mathbb E[e^{t(X-1)}]=e^{-t}(1-t/a)^{-a}.$$ The shape–rate convention makes $X$ mean one. This exact formula underlies the coordinate and projected concentration estimates.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L345-L371

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

theorem ReweightedNPMLE.centered_gamma_mgf {a t : ℝ} (ha : 0 < a) (ht : t < a) :
    ∫ x, Real.exp (t * (x - 1)) ∂gammaMeasure a a =
      Real.exp (-t) * (1 - t / a) ^ (-a) := by sorry
