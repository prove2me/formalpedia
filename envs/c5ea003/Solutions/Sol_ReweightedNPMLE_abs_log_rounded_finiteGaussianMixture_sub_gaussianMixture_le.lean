-- Prove2me | solution 1 for ReweightedNPMLE.abs_log_rounded_finiteGaussianMixture_sub_gaussianMixture_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:00:54.020931+00:00
-- url     : https://prove2.me/submissions/cee748ff-ac66-4a22-85ce-acbb5a9a60f7

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
import Theorems.Thm_ReweightedNPMLE_abs_log_finiteGaussianMixture_rounding_le
import Theorems.Thm_ReweightedNPMLE_abs_log_sub_log_le_two_mul_of_relative_error
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE





























theorem finiteGaussianMixture_pos {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (x : Point d) :
    0 < finiteGaussianMixture w θ x := by
  have hsumpos : 0 < ∑ i, w i := by rw [hsum]; norm_num
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun i (_ : i ∈ Finset.univ) ↦ hw i).mp hsumpos
  unfold finiteGaussianMixture
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j) (gaussianKernel_pos d x (θ j)).le
  · exact ⟨i, Finset.mem_univ i, mul_pos hi (gaussianKernel_pos d x (θ i))⟩

































end ReweightedNPMLE
end

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- End-to-end local log estimate: a relative moment-matching error followed
by location and weight rounding. -/
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (w v : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {T S ε ρ : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2)
    (hρ : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hrelative :
      |finiteGaussianMixture w θ x / gaussianMixture μ ϑ x - 1| ≤ ρ) :
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (gaussianMixture μ ϑ x)| ≤
      (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| + 2 * ρ := by
  have hround := abs_log_finiteGaussianMixture_rounding_le
    w v θ η x hw hv hwsum hvsum hT hS hε hx hθ hη hθη hweightSmall
  have hmoment := abs_log_sub_log_le_two_mul_of_relative_error
    (finiteGaussianMixture_pos θ hw hwsum x)
    (gaussianMixture_pos μ ϑ hϑmeas x) hρ hρhalf hrelative
  calc
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (gaussianMixture μ ϑ x)| =
        |(Real.log (finiteGaussianMixture v η x) -
            Real.log (finiteGaussianMixture w θ x)) +
          (Real.log (finiteGaussianMixture w θ x) -
            Real.log (gaussianMixture μ ϑ x))| := by ring
    _ ≤ |Real.log (finiteGaussianMixture v η x) -
          Real.log (finiteGaussianMixture w θ x)| +
        |Real.log (finiteGaussianMixture w θ x) -
          Real.log (gaussianMixture μ ϑ x)| := abs_add_le _ _
    _ ≤ ((T + S) * ε +
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            ∑ i, |v i - w i|) + 2 * ρ := add_le_add hround hmoment
    _ = (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| + 2 * ρ := by ring
