-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
-- name    : Mpfx.FiniteFormat.IsOdd.neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:40:31.843015+00:00
-- url     : https://prove2.me/theorems/eedcecc8-1222-40dd-a055-5943a3a7ac85
-- title:
--   Is Odd: neg iff
-- statement:
--   Iff form of `IsOdd.neg`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L68-L70
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L68-L70

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.IsOdd.neg_iff {F : FiniteFormat} (y : Dyadic) :
    IsOdd F (-y) ↔ IsOdd F y := by sorry
