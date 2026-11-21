-- Prove2me | Theorems.Thm_Mpfx_Format_unbounded_specials
-- name    : Mpfx.Format.unbounded_specials
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:29.908533+00:00
-- url     : https://prove2.me/theorems/39a49737-19ce-4ab1-b573-ac73573fcdac
-- title:
--   Format: unbounded specials
-- statement:
--   The Format construction uses the unbounded specials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L101-L101
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L101-L101

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.unbounded_specials (F : Format) : F.unbounded.specials = F.specials := by sorry

attribute [defeq] Mpfx.Format.unbounded_specials
