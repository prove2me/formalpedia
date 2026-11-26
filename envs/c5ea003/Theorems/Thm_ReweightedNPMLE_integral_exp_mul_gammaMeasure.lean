-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_exp_mul_gammaMeasure
-- name    : ReweightedNPMLE.integral_exp_mul_gammaMeasure
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:33.752941+00:00
-- url     : https://prove2.me/theorems/e977213e-0e01-41e3-b180-0168059f71fa
-- title:
--   Exponential-moment integral for a shape–rate Gamma law
-- statement:
--   For $a,r>0$ and $t<r$, a random variable $X\sim\operatorname{Gamma}(a,r)$ satisfies $$\mathbb E[e^{tX}]=\frac{r^a}{\Gamma(a)}\left(\frac1{r-t}\right)^a\Gamma(a).$$ The displayed form retains the normalization and Gamma-integral factors used in the formal proof; it is the standard Gamma moment-generating formula.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L78-L118

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

theorem ReweightedNPMLE.integral_exp_mul_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂gammaMeasure a r =
      r ^ a / Real.Gamma a * (1 / (r - t)) ^ a * Real.Gamma a := by sorry
