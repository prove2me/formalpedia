-- Prove2me | Theorems.Thm_Mpfx_boundOK_of_abs_le
-- name    : Mpfx.boundOK_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:17.520392+00:00
-- url     : https://prove2.me/theorems/1ba9e5fe-0875-41af-a666-779ce8e3f9ec
-- title:
--   Mpfx: bound OK of abs le
-- statement:
--   If `|g| ≤ |h|` (over ℝ) and `h` is in-bound, so is `g`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L579-L589
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L579-L589

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.boundOK_of_abs_le {b : Bound} {g h : Dyadic}
    (hle : |(g : ℝ)| ≤ |(h : ℝ)|) (hb : Format.boundOK b h) :
    Format.boundOK b g := by sorry
