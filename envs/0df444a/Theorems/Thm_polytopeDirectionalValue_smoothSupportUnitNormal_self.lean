-- Prove2me | Theorems.Thm_polytopeDirectionalValue_smoothSupportUnitNormal_self
-- name    : polytopeDirectionalValue_smoothSupportUnitNormal_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:32.462639+00:00
-- url     : https://prove2.me/theorems/52a0e25c-c677-5b11-96cd-b370631f15a8
-- title:
--   polytope Directional Value smooth Support Unit Normal self: polytope Directional Value smooth Support Unit Normal self
-- statement:
--   A unit normal has directional value one in its own direction.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L270-L275
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L270-L275

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem polytopeDirectionalValue_smoothSupportUnitNormal_self
    (theta : ℝ) :
    polytopeDirectionalValue (smoothSupportUnitNormal theta) theta = 1 := by sorry
