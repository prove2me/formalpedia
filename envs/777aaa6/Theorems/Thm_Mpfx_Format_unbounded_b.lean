-- Prove2me | Theorems.Thm_Mpfx_Format_unbounded_b
-- name    : Mpfx.Format.unbounded_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:34.962188+00:00
-- url     : https://prove2.me/theorems/940dffad-8c3b-4ecd-9e23-644e4f5759ec
-- title:
--   Format: unbounded b
-- statement:
--   The Format construction uses the unbounded b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L100-L100
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L100-L100

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.unbounded_b (F : Format) : F.unbounded.b = ⊤ := by sorry

attribute [defeq] Mpfx.Format.unbounded_b
