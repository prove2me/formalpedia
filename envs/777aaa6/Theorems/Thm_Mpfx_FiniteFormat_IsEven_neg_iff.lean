-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
-- name    : Mpfx.FiniteFormat.IsEven.neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:40:53.813821+00:00
-- url     : https://prove2.me/theorems/f21811b9-af36-492b-a3e0-244388c029cc
-- title:
--   Is Even: neg iff
-- statement:
--   Iff form of `IsEven.neg`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L90-L92
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L90-L92

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.IsEven.neg_iff {F : FiniteFormat} (y : Dyadic) :
    IsEven F (-y) ↔ IsEven F y := by sorry
