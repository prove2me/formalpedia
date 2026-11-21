-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_zero
-- name    : Mpfx.canonicalExp_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:16.882941+00:00
-- url     : https://prove2.me/theorems/8ac1cb12-ec64-4dfd-9e00-0e57cc418cef
-- title:
--   Mpfx: canonical Exp zero
-- statement:
--   With a minimum quantum, `canonicalExp` at `0` is that quantum.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L482-L487
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L482-L487

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_zero (F : FiniteFormat) {e : ℤ} (hexp : F.exp = (e : QExp)) :
    F.canonicalExp 0 = e := by sorry
