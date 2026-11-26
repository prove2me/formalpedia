-- Prove2me | Theorems.Thm_selfAdjoint_generates_unitary_group_generator
-- name    : selfAdjoint_generates_unitary_group_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:15.934573+00:00
-- url     : https://prove2.me/theorems/5e8c64ec-00be-47d8-b993-3aea1dc694d2
-- title:
--   self Adjoint generates unitary group generator: self Adjoint generates unitary group generator
-- statement:
--   The phase unitary group constructed from a self-adjoint operator has generator `A`.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Theorem.lean#L656-L661
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Theorem.lean#L656-L661

import Definitions.Def_Spectral_Stone_SelfAdjoint
import Definitions.Def_Spectral_Spectral_Existence
import Definitions.Def_Spectral_Stone_Theorem
set_option autoImplicit false
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem selfAdjoint_generates_unitary_group_generator
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    (selfAdjoint_generates_unitary_group A hA).generator = A := by sorry
