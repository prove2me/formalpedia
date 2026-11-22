-- Prove2me | Theorems.Thm_Mpfx_rndUp_le_rndDown_add_ulp
-- name    : Mpfx.rndUp_le_rndDown_add_ulp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:46.657926+00:00
-- url     : https://prove2.me/theorems/858514a3-d609-4802-91f5-d0aa14962191
-- title:
--   Mpfx: rnd Up le rnd Down add ulp
-- statement:
--   The round-up is within one ulp of the round-down.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L139-L161
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L139-L161

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndUp_le_rndDown_add_ulp (F : FiniteFormat) (x : ℝ) :
    (rndUp F x : ℝ) ≤ (rndDown F x : ℝ) + ulp F x := by sorry
