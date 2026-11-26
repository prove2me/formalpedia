-- Prove2me | Theorems.Thm_cayleyTransform_apply_plus
-- name    : cayleyTransform_apply_plus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:28.794276+00:00
-- url     : https://prove2.me/theorems/9e4eb902-b00d-5b55-a11b-6959914de3a0
-- title:
--   cayley Transform apply plus: cayley Transform apply plus
-- statement:
--   The Cayley transform sends `(A + iI)x` to `(A - iI)x`.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L303-L310
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L303-L310

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic
set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem cayleyTransform_apply_plus
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (x : A.domain) :
    cayleyTransform A hA (A x + Complex.I • (x : E)) =
      A x - Complex.I • (x : E) := by sorry
