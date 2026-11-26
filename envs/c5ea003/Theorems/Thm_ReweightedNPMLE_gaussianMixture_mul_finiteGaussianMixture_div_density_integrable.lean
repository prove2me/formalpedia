-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
-- name    : ReweightedNPMLE.gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:42:03.337551+00:00
-- url     : https://prove2.me/theorems/d6900f3e-c05b-57ca-99fa-649fa679b24d
-- title:
--   Integrability of a general–finite Gaussian overlap
-- statement:
--   Let \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\). Let \(\mu\) be a probability measure on \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and set \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). For a finite index set \(I\), set \(q(x)=\sum_iw_i\phi_d(x-z_i)\). Assume \(S\ge0\), \(\|\theta(a)\|\le S\) for all \(a\), and \(\|z_i\|\le S\) for all \(i\). The finite coefficients \(w_i\) may be arbitrary real numbers. Then
--   \[
--   x\longmapsto\frac{p(x)q(x)}{\phi_d(x)}
--   \]
--   is Lebesgue integrable. Consequently, the weighted cross term between a general probability mixture and a finite signed mixture is well defined without imposing nonnegativity or normalization on the finite coefficients.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasureHellinger.lean#L15-L43

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

theorem ReweightedNPMLE.gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    Integrable (fun x : Point d ↦
      gaussianMixture μ θ x * finiteGaussianMixture w z x /
        gaussianDensity d x) := by sorry
