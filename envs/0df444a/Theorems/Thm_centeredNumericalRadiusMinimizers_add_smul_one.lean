-- Prove2me | Theorems.Thm_centeredNumericalRadiusMinimizers_add_smul_one
-- name    : centeredNumericalRadiusMinimizers_add_smul_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:50.453087+00:00
-- url     : https://prove2.me/theorems/49cd1248-1990-592e-a71f-07e03bf6729a
-- title:
--   centered Numerical Radius Minimizers add smul one: centered Numerical Radius Minimizers add smul one
-- statement:
--   Adding `bI` to an operator translates every optimal center by `b`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L263-L283
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L263-L283

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

theorem centeredNumericalRadiusMinimizers_add_smul_one
    (A : E →L[ℂ] E) (b : ℂ) :
    centeredNumericalRadiusMinimizers (A + b • 1) =
      (fun c : ℂ => c + b) '' centeredNumericalRadiusMinimizers A := by sorry
