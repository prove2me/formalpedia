-- Prove2me | Theorems.Thm_exists_real_mem_centeredNumericalRadiusMinimizers
-- name    : exists_real_mem_centeredNumericalRadiusMinimizers
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:53.042399+00:00
-- url     : https://prove2.me/theorems/28683496-f4dd-4130-a629-241bd1c44fbc
-- title:
--   exists real mem centered Numerical Radius Minimizers: exists real mem centered Numerical Radius Minimizers
-- statement:
--   A self-adjoint operator has a real globally optimal scalar center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L459-L479
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L459-L479

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

theorem exists_real_mem_centeredNumericalRadiusMinimizers
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ r : ℝ, (r : ℂ) ∈ centeredNumericalRadiusMinimizers A := by sorry
