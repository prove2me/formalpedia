-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_smul_add_smul_one
-- name    : centeredNumericalRadiusMinimizers_smul_add_smul_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:08:13.759153+00:00
-- url     : https://prove2.me/theorems/49acddcd-a809-424d-a77e-3e9ac4a3b6de
-- title:
--   centered Numerical Radius Minimizers smul add smul one: centered Numerical Radius Minimizers smul add smul one
-- statement:
--   An invertible affine change `A ↦ aA+bI` carries optimal centers by the
--   same affine map.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L329-L334
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L329-L334

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
omit [Nontrivial E]

theorem centeredNumericalRadiusMinimizers_smul_add_smul_one
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    centeredNumericalRadiusMinimizers (a • A + b • 1) =
      (fun c : ℂ => a * c + b) '' centeredNumericalRadiusMinimizers A := by sorry
