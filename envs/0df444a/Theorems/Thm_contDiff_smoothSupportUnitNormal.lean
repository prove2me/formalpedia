-- Prove2me | Theorems.Thm_contDiff_smoothSupportUnitNormal
-- name    : contDiff_smoothSupportUnitNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:57.312116+00:00
-- url     : https://prove2.me/theorems/3b0dc856-a257-490c-99bd-0f2085a46954
-- title:
--   cont Diff smooth Support Unit Normal: cont Diff smooth Support Unit Normal
-- statement:
--   The unit normal is infinitely differentiable.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L72-L74
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L72-L74

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_smoothSupportUnitNormal :
    ContDiff ℝ ∞ smoothSupportUnitNormal := by sorry
