-- Prove2me | Theorems.Thm_Mpfx_Format_boundOK_neg_iff
-- name    : Mpfx.Format.boundOK_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:29.011047+00:00
-- url     : https://prove2.me/theorems/ea02b96c-b788-47e7-b8ea-91ffbeb74c82
-- title:
--   Format: bound OK neg iff
-- statement:
--   The Format construction uses the bound OK neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L142-L144
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L142-L144

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.boundOK_neg_iff (b : Bound) (d : Dyadic) :
    boundOK b (-d) ↔ boundOK b d := by sorry
