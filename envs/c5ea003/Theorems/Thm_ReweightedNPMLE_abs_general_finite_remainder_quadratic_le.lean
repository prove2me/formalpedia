-- Prove2me | Theorems.Thm_ReweightedNPMLE_abs_general_finite_remainder_quadratic_le
-- name    : ReweightedNPMLE.abs_general_finite_remainder_quadratic_le
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:36:13.148915+00:00
-- url     : https://prove2.me/theorems/fb303933-d1ab-584d-83d5-1e734e5ba0b9
-- title:
--   A fourfold Taylor-tail bound for the remainder quadratic form
-- statement:
--   Let \(\mu\) be a probability measure and \(\theta:\Theta\to\mathbb R^d\) measurable. Let \(w_i\ge0\) with \(\sum_iw_i=1\), and let \(z_i\in\mathbb R^d\). Assume \(S\ge0\), \(\|\theta(a)\|\le S\) for all \(a\), and \(\|z_i\|\le S\) for all \(i\). For \(L\in\mathbb N\), put \(T_L(u,v)=\sum_{\ell=0}^L\langle u,v\rangle^\ell/\ell!\) and \(R_L(u,v)=e^{\langle u,v\rangle}-T_L(u,v)\). For a kernel \(K\), define
--   \[
--   \mathcal Q(K)=\iint K(\theta(b),\theta(a))\,d\mu(b)d\mu(a)
--   -2\sum_iw_i\int K(\theta(a),z_i)\,d\mu(a)
--   +\sum_{i,j}w_iw_jK(z_i,z_j).
--   \]
--   Then
--   \[
--   |\mathcal Q(R_L)|\le4\,\frac{e^{S^2}(S^2)^{L+1}}{(L+1)!}.
--   \]
--   No equality of moments is assumed in this remainder estimate.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasureHellinger.lean#L341-L429

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

theorem ReweightedNPMLE.abs_general_finite_remainder_quadratic_le
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    |(∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j)| ≤
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) := by sorry
