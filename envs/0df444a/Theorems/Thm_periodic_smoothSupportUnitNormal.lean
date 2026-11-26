-- Prove2me | Theorems.Thm_periodic_smoothSupportUnitNormal
-- name    : periodic_smoothSupportUnitNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:00.200619+00:00
-- url     : https://prove2.me/theorems/aa786462-fe7c-409f-990c-a766698f618d
-- title:
--   periodic smooth Support Unit Normal: periodic smooth Support Unit Normal
-- statement:
--   The unit normal is `2*pi`-periodic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L51-L53
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L51-L53

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_smoothSupportUnitNormal :
    Function.Periodic smoothSupportUnitNormal (2 * Real.pi) := by sorry
