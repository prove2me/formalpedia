-- Prove2me | Theorems.Thm_realContinuousLinearMapCoefficient_im
-- name    : realContinuousLinearMapCoefficient_im
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:57.786379+00:00
-- url     : https://prove2.me/theorems/d98f4e64-2c5a-5689-a958-a889cb552ea7
-- title:
--   real Continuous Linear Map Coefficient im: real Continuous Linear Map Coefficient im
-- statement:
--   The real Continuous Linear Map Coefficient im construction uses the real Continuous Linear Map Coefficient im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PlanarDualDirection.lean#L40-L42
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PlanarDualDirection.lean#L40-L42

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_PlanarDualDirection
set_option autoImplicit false
open Complex

theorem realContinuousLinearMapCoefficient_im
    (f : ℂ →L[ℝ] ℝ) :
    (realContinuousLinearMapCoefficient f).im = f I := by sorry

attribute [defeq] realContinuousLinearMapCoefficient_im
