-- Prove2me | Theorems.Thm_ReweightedNPMLE_integrable_exp_mul_gammaMeasure
-- name    : ReweightedNPMLE.integrable_exp_mul_gammaMeasure
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:35.682862+00:00
-- url     : https://prove2.me/theorems/426cd36d-7c65-499e-8965-a8134cae21a4
-- title:
--   Integrability of Gamma exponential moments below the rate
-- statement:
--   Let $X$ have the shape–rate Gamma distribution $\operatorname{Gamma}(a,r)$, with $a,r>0$. For every real $t<r$, $$\mathbb E[e^{tX}]<\infty.$$ Formally, the exponential is Bochner integrable under the Gamma measure. This permits subsequent moment and Chernoff calculations.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L40-L76

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

theorem ReweightedNPMLE.integrable_exp_mul_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x ↦ Real.exp (t * x)) (gammaMeasure a r) := by sorry
