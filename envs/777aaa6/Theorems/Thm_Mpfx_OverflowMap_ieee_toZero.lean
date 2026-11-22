-- Prove2me | Theorems.Thm_Mpfx_OverflowMap_ieee_toZero
-- name    : Mpfx.OverflowMap.ieee_toZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:29:41.16343+00:00
-- url     : https://prove2.me/theorems/a0be44e5-c189-46fe-9b1d-aa4f25351dd4
-- title:
--   Overflow Map: ieee to Zero
-- statement:
--   The IEEE RTZ map is the saturating one.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L135-L136
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L135-L136

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Special
set_option autoImplicit true
open Mpfx
open Mpfx.OverflowMap

theorem Mpfx.OverflowMap.ieee_toZero (F : FiniteFormat) (hb : F.b ≠ ⊤) (hinf) :
    OverflowMap.ieee F .toZero hb hinf = OverflowMap.saturate F hb := by sorry
