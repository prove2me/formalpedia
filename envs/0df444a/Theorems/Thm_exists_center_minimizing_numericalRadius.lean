-- Prove2me | Theorems.Thm_exists_center_minimizing_numericalRadius
-- name    : exists_center_minimizing_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:34.3916+00:00
-- url     : https://prove2.me/theorems/36513e81-28f7-538a-a925-248c4d173f7c
-- title:
--   exists center minimizing numerical Radius: exists center minimizing numerical Radius
-- statement:
--   There is a center minimizing the numerical radius of the scalar
--   translate `A-cI`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L181-L185
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L181-L185

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

theorem exists_center_minimizing_numericalRadius (A : E →L[ℂ] E) :
    ∃ c : ℂ, ∀ d : ℂ,
      numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1) := by sorry
