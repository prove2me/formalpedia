-- Prove2me | solution 1 for ReweightedNPMLE.log_one_add_ge_sub_sq_half
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:09:44.584752+00:00
-- url     : https://prove2.me/submissions/5c5c2b80-5854-45b8-a6ca-2c84818c373e

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {u : ℝ}
    (hlower : -(1 / 2 : ℝ) ≤ u) :
    u - u ^ 2 ≤ Real.log (1 + u) := by
  let f : ℝ → ℝ := fun x ↦ Real.log (1 + x) - x + x ^ 2
  have hfderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt f (x * (1 + 2 * x) / (1 + x)) x := by
    intro x hx
    have hne : 1 + x ≠ 0 := by linarith
    have hlog := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hne
    convert (hlog.sub (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [Pi.add_apply, Pi.one_apply, id_eq] <;> field_simp <;> ring
  by_cases hu0 : 0 ≤ u
  · have hmono : MonotoneOn f (Set.Icc 0 u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      · intro x hx
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        exact div_nonneg (mul_nonneg hx.1.le (by linarith [hx.1])) (by linarith [hx.1])
    have h := hmono (left_mem_Icc.mpr hu0) (right_mem_Icc.mpr hu0) hu0
    dsimp [f] at h
    norm_num at h
    linarith
  · have hule : u ≤ 0 := le_of_not_ge hu0
    have hanti : AntitoneOn f (Set.Icc u 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc u 0)
      · intro x hx
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        have hlin : 0 ≤ 1 + 2 * x := by linarith [hx.1]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hx.2.le hlin) (by linarith [hx.1])
    have h := hanti (left_mem_Icc.mpr hule) (right_mem_Icc.mpr hule) hule
    dsimp [f] at h
    norm_num at h
    linarith
