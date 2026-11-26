-- Prove2me | solution 1 for ReweightedNPMLE.gaussianKernel_location_exp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:26.747313+00:00
-- url     : https://prove2.me/submissions/1a2b11e8-a16d-4b81-837f-128d012810df

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
import Theorems.Thm_ReweightedNPMLE_abs_gaussianScore_sub_le

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































/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































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
/-- Pointwise multiplicative comparison of two translated Gaussian kernels
whose locations are close. -/
theorem solution {d : ℕ} (x θ η : Point d)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S)
    (hθη : ‖θ - η‖ ≤ ε) :
    Real.exp (-((T + S) * ε)) * gaussianKernel d x θ ≤
        gaussianKernel d x η ∧
      gaussianKernel d x η ≤
        Real.exp ((T + S) * ε) * gaussianKernel d x θ := by
  let c := (T + S) * ε
  have hscore := abs_gaussianScore_sub_le x θ η hT hS hε hx hθ hη hθη
  have hdiff :
      -c ≤ gaussianScore x η - gaussianScore x θ ∧
        gaussianScore x η - gaussianScore x θ ≤ c := by
    dsimp [c]
    have habs : |gaussianScore x η - gaussianScore x θ| ≤ (T + S) * ε := by
      simpa only [abs_sub_comm] using hscore
    exact (abs_le.mp habs)
  have hkernel : gaussianKernel d x η = gaussianKernel d x θ *
      Real.exp (gaussianScore x η - gaussianScore x θ) := by
    rw [gaussianKernel_eq_density_mul_exp_score,
      gaussianKernel_eq_density_mul_exp_score, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  constructor
  · calc
      Real.exp (-c) * gaussianKernel d x θ =
          gaussianKernel d x θ * Real.exp (-c) := by ring
      _ ≤ gaussianKernel d x θ *
          Real.exp (gaussianScore x η - gaussianScore x θ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiff.1)
          (gaussianKernel_pos d x θ).le
      _ = gaussianKernel d x η := hkernel.symm
  · rw [hkernel]
    calc
      gaussianKernel d x θ *
          Real.exp (gaussianScore x η - gaussianScore x θ) ≤
          gaussianKernel d x θ * Real.exp c :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiff.2)
          (gaussianKernel_pos d x θ).le
      _ = Real.exp c * gaussianKernel d x θ := by ring
