-- Prove2me | Theorems.Thm_Mpfx_zpow_log_le_rndDown
-- name    : Mpfx.zpow_log_le_rndDown
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:57:40.240227+00:00
-- url     : https://prove2.me/theorems/c39675bc-d55f-4f73-9c5d-76b9960252ef
-- title:
--   Mpfx: zpow log le rnd Down
-- statement:
--   Above `F`'s coarsest step, the round-down stays inside `x`'s binade.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L310-L320
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L310-L320

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.zpow_log_le_rndDown (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hq : F.IsAboveQuantum x) :
    (2 : ℝ) ^ (Int.log 2 x) ≤ ((rndDown F x : Dyadic) : ℝ) := by sorry
