-- Prove2me | Theorems.Thm_numericalRadiusSeminorm_apply
-- name    : numericalRadiusSeminorm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:40.854354+00:00
-- url     : https://prove2.me/theorems/25e56130-9e98-4d88-9992-2512f3ec21a2
-- title:
--   numerical Radius Seminorm apply: numerical Radius Seminorm apply
-- statement:
--   The numerical Radius Seminorm apply construction uses the numerical Radius Seminorm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L273-L274
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L273-L274

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadiusSeminorm_apply (A : E →L[ℂ] E) :
    numericalRadiusSeminorm A = numericalRadius A := by sorry

attribute [defeq] numericalRadiusSeminorm_apply
