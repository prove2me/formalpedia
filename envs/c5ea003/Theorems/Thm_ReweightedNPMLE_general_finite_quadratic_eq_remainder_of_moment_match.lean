-- Prove2me | Theorems.Thm_ReweightedNPMLE_general_finite_quadratic_eq_remainder_of_moment_match
-- name    : ReweightedNPMLE.general_finite_quadratic_eq_remainder_of_moment_match
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:47.60857+00:00
-- url     : https://prove2.me/theorems/4fbd11a9-effa-4f00-856d-d1b7d2d015e6
-- title:
--   Reduction of the exponential quadratic form to its Taylor remainder
-- statement:
--   Let \(\mu\) be a probability measure, let \(\theta:\Theta\to\mathbb R^d\) be measurable, and let \(w_i\in\mathbb R,z_i\in\mathbb R^d\) be finite families. Assume \(S\ge0\), \(\|\theta(a)\|\le S\) for all \(a\), and \(\|z_i\|\le S\) for all \(i\). Assume all monomials of degree at most \(L\) are integrable under the parameter map and satisfy \(\int\theta(a)^\alpha\,d\mu(a)=\sum_iw_i z_i^\alpha\) for every multi-index \(|\alpha|\le L\). For \(L\in\mathbb N\), put \(T_L(u,v)=\sum_{\ell=0}^L\langle u,v\rangle^\ell/\ell!\) and \(R_L(u,v)=e^{\langle u,v\rangle}-T_L(u,v)\). For a kernel \(K\), define
--   \[
--   \mathcal Q(K)=\iint K(\theta(b),\theta(a))\,d\mu(b)d\mu(a)
--   -2\sum_iw_i\int K(\theta(a),z_i)\,d\mu(a)
--   +\sum_{i,j}w_iw_jK(z_i,z_j).
--   \]
--   Then \(\mathcal Q(K_{\exp})=\mathcal Q(R_L)\), where \(K_{\exp}(u,v)=e^{\langle u,v\rangle}\). The finite coefficients need not be nonnegative.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasureHellinger.lean#L438-L529

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

theorem ReweightedNPMLE.general_finite_quadratic_eq_remainder_of_moment_match
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
        ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) =
      (∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j) := by sorry
