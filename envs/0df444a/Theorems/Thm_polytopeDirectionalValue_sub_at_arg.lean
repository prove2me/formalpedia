-- Prove2me | Theorems.Thm_polytopeDirectionalValue_sub_at_arg
-- name    : polytopeDirectionalValue_sub_at_arg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:43.267009+00:00
-- url     : https://prove2.me/theorems/6c8257f6-eb97-4821-96ad-d24ce5f02d26
-- title:
--   polytope Directional Value sub at arg: polytope Directional Value sub at arg
-- statement:
--   Looking in the direction of a nonzero displacement recovers its norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L18-L29
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L18-L29

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem polytopeDirectionalValue_sub_at_arg
    {z w : ℂ} (hzw : z ≠ w) :
    polytopeDirectionalValue z (z - w).arg -
        polytopeDirectionalValue w (z - w).arg = ‖z - w‖ := by sorry
