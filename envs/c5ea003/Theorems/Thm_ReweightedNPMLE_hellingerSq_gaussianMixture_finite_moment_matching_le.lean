-- Prove2me | Theorems.Thm_ReweightedNPMLE_hellingerSq_gaussianMixture_finite_moment_matching_le
-- name    : ReweightedNPMLE.hellingerSq_gaussianMixture_finite_moment_matching_le
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:43:58.341006+00:00
-- url     : https://prove2.me/theorems/1ebb6dbf-35eb-5726-b6f0-d932e7f86ed3
-- title:
--   A factorial Hellinger approximation bound from moment matching
-- statement:
--   Let \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\). Let \(\mu\) be a probability measure on \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and set \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). For a finite index set \(I\), set \(q(x)=\sum_iw_i\phi_d(x-z_i)\). Assume \(S\ge0\), \(\|\theta(a)\|\le S\) for all \(a\), and \(\|z_i\|\le S\) for all \(i\). Suppose \(w_i\ge0\), \(\sum_iw_i=1\), and all monomials through degree \(L\) are integrable and matched:
--   \(\int\theta(a)^\alpha\,d\mu(a)=\sum_iw_i z_i^\alpha\) for \(|\alpha|\le L\). With \(H^2(p,q)=\int(\sqrt p-\sqrt q)^2dx\),
--   \[
--   H^2(p,q)\le
--   \left(4\,\frac{e^{S^2}(S^2)^{L+1}}{(L+1)!}\right)^{1/2}.
--   \]
--   This controls the discrepancy globally on observation space.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasureHellinger.lean#L579-L633

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

theorem ReweightedNPMLE.hellingerSq_gaussianMixture_finite_moment_matching_le
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
    hellingerSq volume (gaussianMixture μ θ) (finiteGaussianMixture w z) ≤
      (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial)) ^ (1 / 2 : ℝ) := by sorry
