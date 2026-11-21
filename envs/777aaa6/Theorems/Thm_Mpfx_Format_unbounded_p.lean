-- Prove2me | Theorems.Thm_Mpfx_Format_unbounded_p
-- name    : Mpfx.Format.unbounded_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:50.060127+00:00
-- url     : https://prove2.me/theorems/482ad4a8-49a4-4fd9-a4f5-9c31485fc733
-- title:
--   Format: unbounded p
-- statement:
--   The Format construction uses the unbounded p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L98-L98
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L98-L98

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.unbounded_p (F : Format) : F.unbounded.p = F.p := by sorry

attribute [defeq] Mpfx.Format.unbounded_p
