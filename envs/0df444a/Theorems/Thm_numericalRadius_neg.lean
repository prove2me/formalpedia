-- Prove2me | Theorems.Thm_numericalRadius_neg
-- name    : numericalRadius_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:44.163493+00:00
-- url     : https://prove2.me/theorems/4e1bf883-9ce4-49f2-afcf-59457cb4c132
-- title:
--   numerical Radius neg: numerical Radius neg
-- statement:
--   The numerical Radius neg construction uses the numerical Radius neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L256-L258
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L256-L258

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_neg (A : E →L[ℂ] E) :
    numericalRadius (-A) = numericalRadius A := by sorry
