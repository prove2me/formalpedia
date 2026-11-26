-- Prove2me | Theorems.Thm_ReweightedNPMLE_integrableOn_rpow_mul_exp_neg_mul_Ioi
-- name    : ReweightedNPMLE.integrableOn_rpow_mul_exp_neg_mul_Ioi
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:45:06.419832+00:00
-- url     : https://prove2.me/theorems/ffa24072-a25a-4e20-b2e5-c7c10ecb1dc7
-- title:
--   Integrability of the Gamma kernel
-- statement:
--   Let $a>0$ and $r>0$ be real numbers. The function $$x\mapsto x^{a-1}e^{-rx}$$ is Lebesgue integrable on $(0,\infty)$. This supplies the analytic integrability step for Gamma exponential moments.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L24-L38

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

theorem ReweightedNPMLE.integrableOn_rpow_mul_exp_neg_mul_Ioi {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ ↦ x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) := by sorry
