-- Prove2me | Theorems.Thm_smul_add_smul_mem_numericalRange_of_mem_normalized
-- name    : smul_add_smul_mem_numericalRange_of_mem_normalized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:57.491923+00:00
-- url     : https://prove2.me/theorems/a54ee643-4332-45f1-b163-8e408fa8b607
-- title:
--   smul add smul mem numerical Range of mem normalized: smul add smul mem numerical Range of mem normalized
-- statement:
--   The smul add smul mem numerical Range of mem normalized construction uses the smul add smul mem numerical Range of mem normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L69-L87
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L69-L87

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem smul_add_smul_mem_numericalRange_of_mem_normalized (A : E →L[ℂ] E)
    {z₀ z₁ : ℂ} (hz : z₀ ≠ z₁)
    {a b : ℝ} (hab : a + b = 1)
    (hb : (b : ℂ) ∈ numericalRange ((z₁ - z₀)⁻¹ • (A - z₀ • 1))) :
    a • z₀ + b • z₁ ∈ numericalRange A := by sorry
