-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
-- name    : Mpfx.FiniteFormat.IsEven.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:41:12.087952+00:00
-- url     : https://prove2.me/theorems/6c6c84c2-3668-4705-a4a7-782cd8bbb054
-- title:
--   Is Even: neg
-- statement:
--   `IsEven` is invariant under negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L86-L87
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L86-L87

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.IsEven.neg {F : FiniteFormat} {y : Dyadic} (h : IsEven F y) : IsEven F (-y) := by sorry
