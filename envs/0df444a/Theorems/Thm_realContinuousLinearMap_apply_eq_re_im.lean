-- Prove2me | Theorems.Thm_realContinuousLinearMap_apply_eq_re_im
-- name    : realContinuousLinearMap_apply_eq_re_im
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:42.084668+00:00
-- url     : https://prove2.me/theorems/680821cb-193a-521d-843c-c48f2642f21f
-- title:
--   real Continuous Linear Map apply eq re im: real Continuous Linear Map apply eq re im
-- statement:
--   A real continuous linear functional on `ℂ` is determined by its values
--   on the real basis vectors `1` and `I`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PlanarDualDirection.lean#L18-L28
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PlanarDualDirection.lean#L18-L28

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_PlanarDualDirection
set_option autoImplicit false
open Complex

theorem realContinuousLinearMap_apply_eq_re_im
    (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = z.re * f 1 + z.im * f I := by sorry
