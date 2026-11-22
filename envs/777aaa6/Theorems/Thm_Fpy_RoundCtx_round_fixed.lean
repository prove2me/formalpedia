-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_fixed
-- name    : Fpy.RoundCtx.round_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:35:13.819885+00:00
-- url     : https://prove2.me/theorems/59e88eb1-20b2-420a-8719-68b076e09979
-- title:
--   Round Ctx: round fixed
-- statement:
--   FloatToFixed on contexts: `c'` rounds into the fixed-point format at `y`'s
--   canonical exponent in `c`'s format, with `c`'s mode.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L177-L187
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L177-L187

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx

theorem Fpy.RoundCtx.round_fixed {c c' : RoundCtx} (hp1 : c.F.p ≠ ((1 : ℕ) : Prec)) (hb : c.F.b = ⊤)
    (hp' : c'.F.p = ⊤) (hb' : c'.F.b = ⊤) (hrm : c'.rm = c.rm) {y : ℝ}
    (he : c'.F.exp = ((c.F.canonicalExp y : ℤ) : QExp)) :
    c'.round (.finite y) = c.round (.finite y) := by sorry
