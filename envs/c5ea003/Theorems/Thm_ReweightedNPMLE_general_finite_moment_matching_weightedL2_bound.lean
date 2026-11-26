-- Prove2me | Theorems.Thm_ReweightedNPMLE_general_finite_moment_matching_weightedL2_bound
-- name    : ReweightedNPMLE.general_finite_moment_matching_weightedL2_bound
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:43:34.873826+00:00
-- url     : https://prove2.me/theorems/e04aae6e-98ad-4b3d-b268-fa83ae878e72
-- title:
--   A factorial weighted-L² approximation bound from moment matching
-- statement:
--   Let \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\). Let \(\mu\) be a probability measure on \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and set \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). For a finite index set \(I\), set \(q(x)=\sum_iw_i\phi_d(x-z_i)\). Assume \(S\ge0\), \(\|\theta(a)\|\le S\) for all \(a\), and \(\|z_i\|\le S\) for all \(i\). Suppose \(w_i\ge0\) and \(\sum_iw_i=1\). Assume all monomials of degree at most \(L\) are integrable under the parameter map and satisfy \(\int\theta(a)^\alpha\,d\mu(a)=\sum_iw_i z_i^\alpha\) for every multi-index \(|\alpha|\le L\). Then
--   \[
--   \int_{\mathbb R^d}\frac{(p(x)-q(x))^2}{\phi_d(x)}\,dx
--   \le4\,\frac{e^{S^2}(S^2)^{L+1}}{(L+1)!}.
--   \]
--   The error bound applies to an arbitrary bounded-location probability mixture and a finite probability mixture matching its monomials through degree \(L\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasureHellinger.lean#L531-L577

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

theorem ReweightedNPMLE.general_finite_moment_matching_weightedL2_bound
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
        (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
          gaussianDensity d x ≤
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial) := by sorry
