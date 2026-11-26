-- Prove2me | solution 1 for ReweightedNPMLE.finiteGaussianMixture_location_exp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:12.088713+00:00
-- url     : https://prove2.me/submissions/8f2036c6-b781-48f3-997c-3c488a2766d0

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_location_exp_bounds

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Moving all locations of a nonnegative finite mixture gives the same
two-sided exponential comparison as for each component. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε) :
    Real.exp (-((T + S) * ε)) * finiteGaussianMixture w θ x ≤
        finiteGaussianMixture w η x ∧
      finiteGaussianMixture w η x ≤
        Real.exp ((T + S) * ε) * finiteGaussianMixture w θ x := by
  have hcomponent (i : ι) := gaussianKernel_location_exp_bounds
    x (θ i) (η i) hT hS hε hx (hθ i) (hη i) (hθη i)
  constructor
  · unfold finiteGaussianMixture
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      Real.exp (-((T + S) * ε)) * (w i * gaussianKernel d x (θ i)) =
          w i * (Real.exp (-((T + S) * ε)) * gaussianKernel d x (θ i)) := by
        ring
      _ ≤ w i * gaussianKernel d x (η i) :=
        mul_le_mul_of_nonneg_left (hcomponent i).1 (hw i)
  · unfold finiteGaussianMixture
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      w i * gaussianKernel d x (η i) ≤
          w i * (Real.exp ((T + S) * ε) * gaussianKernel d x (θ i)) :=
        mul_le_mul_of_nonneg_left (hcomponent i).2 (hw i)
      _ = Real.exp ((T + S) * ε) *
          (w i * gaussianKernel d x (θ i)) := by ring
