-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_IsOdd_ne_zero
-- name    : Mpfx.FiniteFormat.IsOdd.ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:41:22.48675+00:00
-- url     : https://prove2.me/theorems/ea5976f2-87fd-4127-a987-f4d1c477edec
-- title:
--   Is Odd: ne zero
-- statement:
--   An `IsOdd` value is nonzero.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L73-L76
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L73-L76

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.IsOdd.ne_zero {F : FiniteFormat} {y : Dyadic} (h : IsOdd F y) :
    y ≠ 0 := by sorry
