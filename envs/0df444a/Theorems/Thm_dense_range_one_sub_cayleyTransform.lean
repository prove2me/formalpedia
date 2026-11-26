-- Prove2me | Theorems.Thm_dense_range_one_sub_cayleyTransform
-- name    : dense_range_one_sub_cayleyTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:04.407838+00:00
-- url     : https://prove2.me/theorems/5d085b5d-1f91-4f65-9047-a7d287094003
-- title:
--   dense range one sub cayley Transform: dense range one sub cayley Transform
-- statement:
--   The dense range one sub cayley Transform construction uses the dense range one sub cayley Transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Unitary.lean#L74-L105
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Unitary.lean#L74-L105

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_Cayley_Unitary
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem dense_range_one_sub_cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    DenseRange (fun x => x - cayleyTransform A hA x) := by sorry
