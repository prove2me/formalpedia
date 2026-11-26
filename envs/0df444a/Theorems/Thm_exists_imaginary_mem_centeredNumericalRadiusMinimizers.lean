-- Prove2me | Theorems.Thm_exists_imaginary_mem_centeredNumericalRadiusMinimizers
-- name    : exists_imaginary_mem_centeredNumericalRadiusMinimizers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:22.159455+00:00
-- url     : https://prove2.me/theorems/f5184499-d054-4702-9b70-2c4f2260d1eb
-- title:
--   exists imaginary mem centered Numerical Radius Minimizers: exists imaginary mem centered Numerical Radius Minimizers
-- statement:
--   A skew-adjoint operator has a purely imaginary globally optimal scalar
--   center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L552-L575
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L552-L575

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

theorem exists_imaginary_mem_centeredNumericalRadiusMinimizers
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ, (r : ℂ) * Complex.I ∈ centeredNumericalRadiusMinimizers A := by sorry
