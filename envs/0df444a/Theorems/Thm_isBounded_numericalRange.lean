-- Prove2me | Theorems.Thm_isBounded_numericalRange
-- name    : isBounded_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:45:34.838934+00:00
-- url     : https://prove2.me/theorems/5c6c283e-f421-4f37-a5dd-7b1545242af5
-- title:
--   is Bounded numerical Range: is Bounded numerical Range
-- statement:
--   The numerical range of every bounded operator is a bounded set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L44-L46
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L44-L46

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isBounded_numericalRange (A : E →L[ℂ] E) :
    Bornology.IsBounded (numericalRange A) := by sorry
