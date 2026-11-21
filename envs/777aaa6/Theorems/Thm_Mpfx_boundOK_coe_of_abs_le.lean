-- Prove2me | Theorems.Thm_Mpfx_boundOK_coe_of_abs_le
-- name    : Mpfx.boundOK_coe_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:44.538214+00:00
-- url     : https://prove2.me/theorems/8fb170e9-309f-4613-8644-3801f08b0ab8
-- title:
--   Mpfx: bound OK coe of abs le
-- statement:
--   Converse of `abs_coe_real_le_of_boundOK`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L599-L603
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L599-L603

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.boundOK_coe_of_abs_le {b : NonNegDyadic} {y : Dyadic}
    (h : |(y : ℝ)| ≤ ((b.val : Dyadic) : ℝ)) :
    Format.boundOK ((b : Bound)) y := by sorry
