-- Prove2me | Theorems.Thm_ReweightedNPMLE_euclidean_norm_le_sqrt_card_mul_of_abs_coord_le
-- name    : ReweightedNPMLE.euclidean_norm_le_sqrt_card_mul_of_abs_coord_le
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:42:45.010375+00:00
-- url     : https://prove2.me/theorems/30a34304-6e5c-4a69-be5f-fb32d1f7e620
-- title:
--   Euclidean norm bound from coordinate bounds
-- statement:
--   For a vector $z=(z_1,\ldots,z_d)\in\mathbb R^d$ and $t\ge0$, if $|z_i|\le t$ for all coordinates, then $$\|z\|_2\le\sqrt d\,t.$$ The formal statement converts a coordinate function to the Euclidean-space representation. It includes the zero-dimensional case.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianRadius.lean#L113-L133

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

theorem ReweightedNPMLE.euclidean_norm_le_sqrt_card_mul_of_abs_coord_le
    {d : ℕ} (z : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ i, |z i| ≤ t) :
    ‖WithLp.toLp 2 z‖ ≤ Real.sqrt d * t := by sorry
