-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_smul_one
-- name    : centeredNumericalRadiusMinimizers_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:18.432281+00:00
-- url     : https://prove2.me/theorems/412a4f16-3c76-575c-9ec6-db80a2f799b4
-- title:
--   centered Numerical Radius Minimizers smul one: centered Numerical Radius Minimizers smul one
-- statement:
--   A scalar operator `cI` has the unique optimal center `c`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L354-L359
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L354-L359

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

theorem centeredNumericalRadiusMinimizers_smul_one (c : ℂ) :
    centeredNumericalRadiusMinimizers (c • (1 : E →L[ℂ] E)) = {c} := by sorry
