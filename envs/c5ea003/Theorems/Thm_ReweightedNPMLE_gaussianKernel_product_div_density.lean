-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density
-- name    : ReweightedNPMLE.gaussianKernel_product_div_density
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:57.543294+00:00
-- url     : https://prove2.me/theorems/890ef827-f229-5751-9f76-c5bac449e0f3
-- title:
--   Completed-square identity for Gaussian kernel overlap
-- statement:
--   For any $d\ge0$ and $x,\theta,\eta\in\mathbb R^d$, write $k(x,\theta)=\varphi_d(x-\theta)$ for the standard-covariance Gaussian kernel. Then $$\frac{k(x,\theta)k(x,\eta)}{\varphi_d(x)}=e^{\langle\theta,\eta\rangle}\varphi_d(x-\theta-\eta).$$ This pointwise identity converts weighted Gaussian overlaps into translated Gaussian densities.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Gaussian.lean#L177-L204

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian

/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE

theorem ReweightedNPMLE.gaussianKernel_product_div_density {d : ℕ} (x θ η : Point d) :
    gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x =
      Real.exp (inner ℝ θ η) * gaussianDensity d (x - (θ + η)) := by sorry
