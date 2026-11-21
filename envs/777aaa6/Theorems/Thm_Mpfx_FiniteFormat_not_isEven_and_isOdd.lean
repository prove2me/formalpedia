-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_not_isEven_and_isOdd
-- name    : Mpfx.FiniteFormat.not_isEven_and_isOdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:11.751227+00:00
-- url     : https://prove2.me/theorems/022989af-222d-400f-a731-12a6546a8e4a
-- title:
--   Finite Format: not is Even and is Odd
-- statement:
--   No value is both even and odd.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L95-L97
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L95-L97

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.not_isEven_and_isOdd {F : FiniteFormat} {y : Dyadic}
    (h_even : F.IsEven y) (h_odd : F.IsOdd y) : False := by sorry
