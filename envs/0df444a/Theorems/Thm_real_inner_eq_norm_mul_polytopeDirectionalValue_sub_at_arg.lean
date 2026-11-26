-- Prove2me | Theorems.Thm_real_inner_eq_norm_mul_polytopeDirectionalValue_sub_at_arg
-- name    : real_inner_eq_norm_mul_polytopeDirectionalValue_sub_at_arg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:44.603547+00:00
-- url     : https://prove2.me/theorems/8233796a-8446-44a3-807e-4304c9170d10
-- title:
--   real inner eq norm mul polytope Directional Value sub at arg: real inner eq norm mul polytope Directional Value sub at arg
-- statement:
--   The real inner product with a displacement is its norm times the
--   directional-value difference in the displacement direction.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L33-L48
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L33-L48

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem real_inner_eq_norm_mul_polytopeDirectionalValue_sub_at_arg
    (z v w : ℂ) :
    ⟪z - v, w - v⟫_ℝ =
      ‖z - v‖ *
        (polytopeDirectionalValue w (z - v).arg -
          polytopeDirectionalValue v (z - v).arg) := by sorry
