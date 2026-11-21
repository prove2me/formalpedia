-- Prove2me | Theorems.Thm_Mpfx_Format_mem_neg_iff
-- name    : Mpfx.Format.mem_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:55.592369+00:00
-- url     : https://prove2.me/theorems/3ca667c7-6e27-464d-8b52-f2dcfb64875b
-- title:
--   Format: mem neg iff
-- statement:
--   The Format construction uses the mem neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L151-L152
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L151-L152

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.mem_neg_iff (F : Format) (d : Dyadic) : (-d) ∈ F ↔ d ∈ F := by sorry
