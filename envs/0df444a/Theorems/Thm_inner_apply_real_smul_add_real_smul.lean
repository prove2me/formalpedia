-- Prove2me | Theorems.Thm_inner_apply_real_smul_add_real_smul
-- name    : inner_apply_real_smul_add_real_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:50.188687+00:00
-- url     : https://prove2.me/theorems/1a259a2b-6313-59a0-88f4-a16582124918
-- title:
--   inner apply real smul add real smul: inner apply real smul add real smul
-- statement:
--   The inner apply real smul add real smul construction uses the inner apply real smul add real smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L18-L32
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L18-L32

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_apply_real_smul_add_real_smul (A : E →L[ℂ] E)
    (x₀ x₁ : E) (ω : ℂ) (u v : ℝ) :
    ⟪(u : ℂ) • x₀ + (v : ℂ) • (ω • x₁),
      A ((u : ℂ) • x₀ + (v : ℂ) • (ω • x₁))⟫_ℂ =
    (u : ℂ) ^ 2 * ⟪x₀, A x₀⟫_ℂ +
      ((u * v : ℝ) : ℂ) *
        (ω * ⟪x₀, A x₁⟫_ℂ + starRingEnd ℂ ω * ⟪x₁, A x₀⟫_ℂ) +
      (v : ℂ) ^ 2 * (‖ω‖ ^ 2 : ℂ) * ⟪x₁, A x₁⟫_ℂ := by sorry
