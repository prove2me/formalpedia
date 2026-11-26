-- Prove2me | Theorems.Thm_cayleyTransform_unitary
-- name    : cayleyTransform_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:08.024675+00:00
-- url     : https://prove2.me/theorems/d437b889-553e-42e1-bff7-e881612e92a4
-- title:
--   cayley Transform unitary: cayley Transform unitary
-- statement:
--   The cayley Transform unitary construction uses the cayley Transform unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Unitary.lean#L27-L40
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Unitary.lean#L27-L40

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_Cayley_Unitary
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem cayleyTransform_unitary
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    cayleyTransform A hA ∈ unitary (E →L[ℂ] E) := by sorry
