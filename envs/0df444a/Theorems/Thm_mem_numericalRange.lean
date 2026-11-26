-- Prove2me | Theorems.Thm_mem_numericalRange
-- name    : mem_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:47.252331+00:00
-- url     : https://prove2.me/theorems/d4c559a9-536e-5fe6-983a-32dc61bf5f88
-- title:
--   mem numerical Range: mem numerical Range
-- statement:
--   `z` lies in the numerical range of `A` iff `z = ⟪x, A x⟫_ℂ` for some unit
--   vector `x`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Basic.lean#L34-L36
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Basic.lean#L34-L36

import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_Operator_NumericalRange_Basic
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem mem_numericalRange (A : E →L[ℂ] E) (z : ℂ) :
    z ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z := by sorry
