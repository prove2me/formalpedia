-- Prove2me | Theorems.Thm_norm_le_of_mem_numericalRange
-- name    : norm_le_of_mem_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:55.63295+00:00
-- url     : https://prove2.me/theorems/4dd99fda-c4bc-558a-8c07-91ca4330f3f8
-- title:
--   norm le of mem numerical Range: norm le of mem numerical Range
-- statement:
--   The numerical range lies in the closed disk of radius `‖A‖`: for a unit vector `x`,
--   Cauchy–Schwarz gives `‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ ≤ ‖A‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L28-L33
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L28-L33

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_le_of_mem_numericalRange (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by sorry
