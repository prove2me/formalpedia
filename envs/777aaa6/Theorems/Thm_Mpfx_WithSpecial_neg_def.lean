-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_neg_def
-- name    : Mpfx.WithSpecial.neg_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:24:06.638562+00:00
-- url     : https://prove2.me/theorems/150096bd-2487-4391-865d-969a7b9fa197
-- title:
--   With Special: neg def
-- statement:
--   The With Special construction uses the neg def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L123-L123
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L123-L123

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.neg_def {α : Type} [Neg α] (v : WithSpecial α) : -v = v.neg := by sorry

attribute [defeq] Mpfx.WithSpecial.neg_def
