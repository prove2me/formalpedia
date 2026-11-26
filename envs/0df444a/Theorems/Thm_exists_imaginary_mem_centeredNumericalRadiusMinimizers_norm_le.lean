-- Prove2me | Theorems.Thm_exists_imaginary_mem_centeredNumericalRadiusMinimizers_norm_le
-- name    : exists_imaginary_mem_centeredNumericalRadiusMinimizers_norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:09:00.393892+00:00
-- url     : https://prove2.me/theorems/ec287c81-3fbe-4f68-a0cb-41bd9fd31d4b
-- title:
--   exists imaginary mem centered Numerical Radius Minimizers norm le: exists imaginary mem centered Numerical Radius Minimizers norm le
-- statement:
--   A skew-adjoint operator has a purely imaginary optimal center in the
--   explicit numerical-radius disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L579-L587
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L579-L587

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

theorem exists_imaginary_mem_centeredNumericalRadiusMinimizers_norm_le
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ,
      (r : ℂ) * Complex.I ∈ centeredNumericalRadiusMinimizers A ∧
        ‖(r : ℂ) * Complex.I‖ ≤ 2 * numericalRadius A := by sorry
