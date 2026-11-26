-- Prove2me | Theorems.Thm_norm_le_numericalRadius
-- name    : norm_le_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:26.916813+00:00
-- url     : https://prove2.me/theorems/cbf08833-17b2-5595-8a72-d21f81f43a4a
-- title:
--   norm le numerical Radius: norm le numerical Radius
-- statement:
--   Every point in the numerical range has modulus at most the numerical
--   radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L61-L71
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L61-L71

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_le_numericalRadius (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ numericalRadius A := by sorry
