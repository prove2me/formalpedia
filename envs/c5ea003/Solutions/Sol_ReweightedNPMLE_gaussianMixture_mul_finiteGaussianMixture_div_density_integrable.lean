-- Prove2me | solution 1 for ReweightedNPMLE.gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:06:25.985475+00:00
-- url     : https://prove2.me/submissions/edb4a5fc-833b-4faf-8029-cc4a8cf7470a

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
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_mul_kernel_div_density_integrable

/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    Integrable (fun x : Point d ↦
      gaussianMixture μ θ x * finiteGaussianMixture w z x /
        gaussianDensity d x) := by
  have hsum : Integrable (fun x : Point d ↦
      ∑ i, w i * (gaussianMixture μ θ x * gaussianKernel d x (z i) /
        gaussianDensity d x)) :=
    integrable_finsetSum Finset.univ fun i _ ↦
      (gaussianMixture_mul_kernel_div_density_integrable
        μ θ hθmeas hS hθS (z i) (hzS i)).const_mul (w i)
  apply hsum.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    unfold finiteGaussianMixture
    change (∑ i, w i * (gaussianMixture μ θ x * gaussianKernel d x (z i) /
        gaussianDensity d x)) =
      gaussianMixture μ θ x * (∑ i, w i * gaussianKernel d x (z i)) /
        gaussianDensity d x
    rw [Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
