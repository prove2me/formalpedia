-- Prove2me | Theorems.Thm_norm_cayleyTransform
-- name    : norm_cayleyTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:30.366581+00:00
-- url     : https://prove2.me/theorems/259c3bb3-1cd8-5a36-8795-50f9b2b1b570
-- title:
--   norm cayley Transform: norm cayley Transform
-- statement:
--   The Cayley transform preserves the norm.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L313-L324
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean#L313-L324

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic
set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_cayleyTransform (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (y : E) : ‖cayleyTransform A hA y‖ = ‖y‖ := by sorry
