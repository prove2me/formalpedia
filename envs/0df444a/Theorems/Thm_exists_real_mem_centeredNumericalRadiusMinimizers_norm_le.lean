-- Prove2me | Theorems.Thm_exists_real_mem_centeredNumericalRadiusMinimizers_norm_le
-- name    : exists_real_mem_centeredNumericalRadiusMinimizers_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:08:23.164793+00:00
-- url     : https://prove2.me/theorems/e979feba-fccc-57c9-8b20-4f217b8d92ee
-- title:
--   exists real mem centered Numerical Radius Minimizers norm le: exists real mem centered Numerical Radius Minimizers norm le
-- statement:
--   A self-adjoint operator has a real optimal center in the explicit
--   numerical-radius disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L483-L489
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L483-L489

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

theorem exists_real_mem_centeredNumericalRadiusMinimizers_norm_le
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ r : ℝ, (r : ℂ) ∈ centeredNumericalRadiusMinimizers A ∧
      ‖(r : ℂ)‖ ≤ 2 * numericalRadius A := by sorry
