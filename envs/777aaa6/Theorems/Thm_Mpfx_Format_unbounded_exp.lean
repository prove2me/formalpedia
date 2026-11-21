-- Prove2me | Theorems.Thm_Mpfx_Format_unbounded_exp
-- name    : Mpfx.Format.unbounded_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:52.673145+00:00
-- url     : https://prove2.me/theorems/4501eb6f-4318-45b8-914b-02e1c5c0053f
-- title:
--   Format: unbounded exp
-- statement:
--   The Format construction uses the unbounded exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L99-L99
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L99-L99

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.unbounded_exp (F : Format) : F.unbounded.exp = F.exp := by sorry

attribute [defeq] Mpfx.Format.unbounded_exp
