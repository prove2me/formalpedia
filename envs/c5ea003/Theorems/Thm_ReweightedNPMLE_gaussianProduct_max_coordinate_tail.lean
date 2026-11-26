-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianProduct_max_coordinate_tail
-- name    : ReweightedNPMLE.gaussianProduct_max_coordinate_tail
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:44:07.898264+00:00
-- url     : https://prove2.me/theorems/b1716209-75d3-5ffa-92b7-09edaa10f919
-- title:
--   Maximum-coordinate tail bound for a standard Gaussian vector
-- statement:
--   Let $Z_1,\ldots,Z_d$ be independent standard normal variables, allowing $d=0$. For $t>0$, $$\Pr\{\exists i:\ |Z_i|>t\}\le2d e^{-t^2/2}.$$ This coordinate bound is used to control the Euclidean norm of the Gaussian noise.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianRadius.lean#L81-L111

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

theorem ReweightedNPMLE.gaussianProduct_max_coordinate_tail (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).real
        {z : Fin d → ℝ | ∃ i, |z i| > t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by sorry
