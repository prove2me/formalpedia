-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_p_pos
-- name    : Mpfx.FiniteFormat.p_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:28.145172+00:00
-- url     : https://prove2.me/theorems/f62e9196-f988-4d30-991f-73d3b5b784af
-- title:
--   Finite Format: p pos
-- statement:
--   `F.pos` at a finite precision: the witness `p` in `F.p = ↑p` is positive.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L273-L276
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L273-L276

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.p_pos {F : FiniteFormat} {p : ℕ} (hp : F.p = (p : Prec)) : 0 < p := by sorry
