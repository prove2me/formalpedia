-- Prove2me | Theorems.Thm_ReweightedNPMLE_moment_matching_truncated_quadratic_zero
-- name    : ReweightedNPMLE.moment_matching_truncated_quadratic_zero
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:06.308874+00:00
-- url     : https://prove2.me/theorems/8ba41469-5bbd-419d-b165-858061080432
-- title:
--   Moment matching cancels the truncated exponential quadratic form
-- statement:
--   Let \(\mu\) be any measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\), and let \(w_i\in\mathbb R,z_i\in\mathbb R^d\) be finite families. Assume all monomials of degree at most \(L\) are integrable under the parameter map and satisfy \(\int\theta(a)^\alpha\,d\mu(a)=\sum_iw_i z_i^\alpha\) for every multi-index \(|\alpha|\le L\). Put \(T_L(u,v)=\sum_{\ell=0}^L\langle u,v\rangle^\ell/\ell!\). For a kernel \(K\), define
--   \[
--   \mathcal Q(K)=\iint K(\theta(b),\theta(a))\,d\mu(b)d\mu(a)
--   -2\sum_iw_i\int K(\theta(a),z_i)\,d\mu(a)
--   +\sum_{i,j}w_iw_jK(z_i,z_j).
--   \]
--   Then \(\mathcal Q(T_L)=0\). Neither a probability assumption on \(\mu\) nor nonnegativity of the \(w_i\) is required.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasureHellinger.lean#L212-L264

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
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE

theorem ReweightedNPMLE.moment_matching_truncated_quadratic_zero
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) (θ : Θ → Point d)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ) :
    (∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointTruncatedInnerExp L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointTruncatedInnerExp L (z i) (z j) = 0 := by sorry
