-- Prove2me | Theorems.Thm_exists_imaginary_center_minimizing_numericalRadius_of_mem_skewAdjoint
-- name    : exists_imaginary_center_minimizing_numericalRadius_of_mem_skewAdjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:08:56.166248+00:00
-- url     : https://prove2.me/theorems/7470c620-b4f3-51ef-a71c-a8dc507121c5
-- title:
--   exists imaginary center minimizing numerical Radius of mem skew Adjoint: exists imaginary center minimizing numerical Radius of mem skew Adjoint
-- statement:
--   For a skew-adjoint operator, the centered numerical radius attains its
--   global minimum at a purely imaginary center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L591-L597
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L591-L597

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]

theorem exists_imaginary_center_minimizing_numericalRadius_of_mem_skewAdjoint
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ, ∀ c : ℂ,
      numericalRadius (A - ((r : ℂ) * Complex.I) • 1) ≤
        numericalRadius (A - c • 1) := by sorry
