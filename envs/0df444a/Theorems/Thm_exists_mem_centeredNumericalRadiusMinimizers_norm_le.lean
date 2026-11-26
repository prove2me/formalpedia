-- Prove2me | Theorems.Thm_exists_mem_centeredNumericalRadiusMinimizers_norm_le
-- name    : exists_mem_centeredNumericalRadiusMinimizers_norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:08:08.934309+00:00
-- url     : https://prove2.me/theorems/764a02df-b69a-5c64-be88-825144c7beca
-- title:
--   exists mem centered Numerical Radius Minimizers norm le: exists mem centered Numerical Radius Minimizers norm le
-- statement:
--   There is a globally minimizing center in the explicit numerical-radius
--   disk of radius `2w(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L253-L259
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L253-L259

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

theorem exists_mem_centeredNumericalRadiusMinimizers_norm_le
    (A : E →L[ℂ] E) :
    ∃ c ∈ centeredNumericalRadiusMinimizers A,
      ‖c‖ ≤ 2 * numericalRadius A := by sorry
