-- Prove2me | Theorems.Thm_Mpfx_rndDown_neg_real
-- name    : Mpfx.rndDown_neg_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:03.518246+00:00
-- url     : https://prove2.me/theorems/b98c6c19-66ef-4334-aea3-cd8b1367f8b1
-- title:
--   Mpfx: rnd Down neg real
-- statement:
--   Round-down of `−x` is the negation of round-up of `x` (real value).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L300-L305
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L300-L305

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_neg_real (F : FiniteFormat) (x : ℝ) :
    (rndDown F (-x) : ℝ) = -(rndUp F x : ℝ) := by sorry
