-- Prove2me | Theorems.Thm_inverseCayley_cayleyTransform
-- name    : inverseCayley_cayleyTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:21.560109+00:00
-- url     : https://prove2.me/theorems/81a34e98-ad70-56ee-8697-27452ffe77c5
-- title:
--   inverse Cayley cayley Transform: inverse Cayley cayley Transform
-- statement:
--   Applying the inverse Cayley transform to the Cayley transform recovers the original operator.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Inverse.lean#L78-L122
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Inverse.lean#L78-L122

import Definitions.Def_Spectral_Cayley_Unitary
import Definitions.Def_Spectral_Cayley_Inverse
import Theorems.Thm_cayleyTransform_unitary
import Theorems.Thm_dense_range_one_sub_cayleyTransform
import Theorems.Thm_one_not_mem_eigenvalues_cayleyTransform

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem inverseCayley_cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    inverseCayley (cayleyTransform A hA) (cayleyTransform_unitary A hA)
      (one_not_mem_eigenvalues_cayleyTransform A hA)
      (dense_range_one_sub_cayleyTransform A hA) = A := by sorry
