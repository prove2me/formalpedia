-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_gaussianKernel_product_div_density
-- name    : ReweightedNPMLE.integral_gaussianKernel_product_div_density
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:39.143602+00:00
-- url     : https://prove2.me/theorems/d496e0b6-9993-539f-91ea-7b7b8d7c7936
-- title:
--   Exact integral of a weighted Gaussian kernel overlap
-- statement:
--   For $\theta,\eta\in\mathbb R^d$, with $k(x,\theta)=\varphi_d(x-\theta)$, $$\int_{\mathbb R^d}\frac{k(x,\theta)k(x,\eta)}{\varphi_d(x)}\,dx=e^{\langle\theta,\eta\rangle}.$$ This identity is the building block for the weighted quadratic-form calculation used in Gaussian mixture approximation.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Gaussian.lean#L206-L224

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

theorem ReweightedNPMLE.integral_gaussianKernel_product_div_density {d : ℕ} (θ η : Point d) :
    ∫ x : Point d,
        gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x =
      Real.exp (inner ℝ θ η) := by sorry
