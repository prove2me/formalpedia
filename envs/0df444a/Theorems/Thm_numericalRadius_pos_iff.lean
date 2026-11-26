-- Prove2me | Theorems.Thm_numericalRadius_pos_iff
-- name    : numericalRadius_pos_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:55:18.127693+00:00
-- url     : https://prove2.me/theorems/6b78334b-f1bf-5482-8f4d-fef638c6475e
-- title:
--   numerical Radius pos iff: numerical Radius pos iff
-- statement:
--   The numerical radius is positive exactly for nonzero operators.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L193-L197
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L193-L197

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_pos_iff (A : E →L[ℂ] E) :
    0 < numericalRadius A ↔ A ≠ 0 := by sorry
