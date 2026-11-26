-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_gaussianMixture_sub_finite_sq_div_density
-- name    : ReweightedNPMLE.integral_gaussianMixture_sub_finite_sq_div_density
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:43:01.7412+00:00
-- url     : https://prove2.me/theorems/61b9cd2e-12f7-5ee0-a98e-00ccbf51c685
-- title:
--   Exponential-kernel formula for general–finite approximation error
-- statement:
--   Let \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\). Let \(\mu\) be a probability measure on \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and set \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). For a finite index set \(I\), set \(q(x)=\sum_iw_i\phi_d(x-z_i)\). Assume \(S\ge0\), \(\|\theta(a)\|\le S\) for all \(a\), and \(\|z_i\|\le S\) for all \(i\). For arbitrary real coefficients \(w_i\),
--   \[
--   \begin{aligned}
--   \int\frac{(p-q)^2}{\phi_d}\,dx
--   ={}&\iint e^{\langle\theta(b),\theta(a)\rangle}\,d\mu(b)d\mu(a)\\
--   &-2\sum_iw_i\int e^{\langle\theta(a),z_i\rangle}\,d\mu(a)
--   +\sum_{i,j}w_iw_j e^{\langle z_i,z_j\rangle}.
--   \end{aligned}
--   \]
--   All observation-space terms are integrable. The identity represents the density approximation error as the exponential-kernel quadratic form of the difference between the general mixing law and the finite signed law.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasureHellinger.lean#L116-L172

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

theorem ReweightedNPMLE.integral_gaussianMixture_sub_finite_sq_div_density
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x =
      (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
        ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) := by sorry
