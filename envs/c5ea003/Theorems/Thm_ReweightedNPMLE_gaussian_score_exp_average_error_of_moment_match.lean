-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussian_score_exp_average_error_of_moment_match
-- name    : ReweightedNPMLE.gaussian_score_exp_average_error_of_moment_match
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:45.21608+00:00
-- url     : https://prove2.me/theorems/abd50bd3-c1ab-50ce-a22f-6a71965c1d5b
-- title:
--   Moment matching bounds the averaged Gaussian exponential remainder
-- statement:
--   For an integer $d\ge0$ and vectors $x,z\in\mathbb R^d$, define the Gaussian score
--   $$
--   s_x(z)=\sum_{j=1}^d x_jz_j-\frac12\sum_{j=1}^d z_j^2.
--   $$
--
--   Let $L\ge0$, let $\mu$ be a probability measure on a measurable space $\Theta$, and let $\theta:\Theta\to\mathbb R^d$. Let $I$ be finite, let $w_i\ge0$ satisfy $\sum_iw_i=1$, and let $z_i\in\mathbb R^d$. Suppose the degree-at-most-$2L$ monomial vector $\Phi_{2L}\circ\theta$ is integrable and
--   $$
--   \sum_{i\in I}w_i\Phi_{2L}(z_i)=\int\Phi_{2L}(\theta(a))\,d\mu(a).
--   $$
--   Fix $x\in\mathbb R^d$ and $B\ge0$. Assume $|s_x(z_i)|\le B$ for every $i$, $|s_x(\theta(a))|\le B$ for $\mu$-almost every $a$, and $a\mapsto e^{s_x(\theta(a))}$ is integrable. Then
--   $$
--   \left|\sum_{i\in I}w_i e^{s_x(z_i)}-\int e^{s_x(\theta(a))}\,d\mu(a)\right|
--   \le 2e^B\frac{B^{L+1}}{(L+1)!}.
--   $$
--   Here $\Phi_{2L}$ contains all monomials through total degree $2L$.
--
--   This is the absolute mixture-approximation estimate obtained by matching the polynomial part of the Gaussian score exponential exactly.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L588-L663

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype

theorem ReweightedNPMLE.gaussian_score_exp_average_error_of_moment_match
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (hw : w ∈ stdSimplex ℝ ι)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (θ a)) μ)
    (hmom : ∑ i, w i • monomialFeature d (2 * L) (z i) =
      ∫ a, monomialFeature d (2 * L) (θ a) ∂μ)
    (x : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzB : ∀ i, |coordinateGaussianScore x (z i)| ≤ B)
    (hθB : ∀ᵐ a ∂μ, |coordinateGaussianScore x (θ a)| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) μ) :
    |(∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
        ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ| ≤
      2 * (Real.exp B * B ^ (L + 1) / (L + 1).factorial) := by sorry
