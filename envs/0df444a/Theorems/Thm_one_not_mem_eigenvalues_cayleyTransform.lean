-- Prove2me | Theorems.Thm_one_not_mem_eigenvalues_cayleyTransform
-- name    : one_not_mem_eigenvalues_cayleyTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:07.569832+00:00
-- url     : https://prove2.me/theorems/a3df789b-3842-499b-aa69-312668e6ed65
-- title:
--   one not mem eigenvalues cayley Transform: one not mem eigenvalues cayley Transform
-- statement:
--   The one not mem eigenvalues cayley Transform construction uses the one not mem eigenvalues cayley Transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Unitary.lean#L42-L72
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Unitary.lean#L42-L72

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_Cayley_Unitary
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem one_not_mem_eigenvalues_cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∀ x, cayleyTransform A hA x = x → x = 0 := by sorry
