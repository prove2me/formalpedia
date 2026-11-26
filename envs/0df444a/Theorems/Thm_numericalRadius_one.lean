-- Prove2me | Theorems.Thm_numericalRadius_one
-- name    : numericalRadius_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:07.781699+00:00
-- url     : https://prove2.me/theorems/0007ee92-c904-404b-81e6-c77393269a55
-- title:
--   numerical Radius one: numerical Radius one
-- statement:
--   The identity operator has numerical radius one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L24-L34
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L24-L34

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

theorem numericalRadius_one :
    numericalRadius (1 : E →L[ℂ] E) = 1 := by sorry
