-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_finiteGaussianMixture_sq_div_density
-- name    : ReweightedNPMLE.integral_finiteGaussianMixture_sq_div_density
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:53.650935+00:00
-- url     : https://prove2.me/theorems/f7f40cc3-c146-57d1-ad15-a8bbd1b94ec3
-- title:
--   Weighted quadratic-form identity for finite signed Gaussian mixtures
-- statement:
--   Let $I$ be a finite index set, $c_i\in\mathbb R$, and $\theta_i\in\mathbb R^d$. Define the possibly signed mixture $f(x)=\sum_{i\in I}c_i\varphi_d(x-\theta_i)$. Then $$\int_{\mathbb R^d}\frac{f(x)^2}{\varphi_d(x)}\,dx=\sum_{i\in I}\sum_{j\in I}c_ic_j e^{\langle\theta_i,\theta_j\rangle}.$$ No positivity or normalization of the coefficients is required. The identity links moment matching to weighted $L^2$ control.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Gaussian.lean#L267-L301

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

theorem ReweightedNPMLE.integral_finiteGaussianMixture_sq_div_density
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    ∫ x, (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x =
      ∑ i, ∑ j, c i * c j * Real.exp (inner ℝ (θ i) (θ j)) := by sorry
