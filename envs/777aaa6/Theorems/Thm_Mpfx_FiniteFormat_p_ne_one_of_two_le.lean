-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_p_ne_one_of_two_le
-- name    : Mpfx.FiniteFormat.p_ne_one_of_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:59.642693+00:00
-- url     : https://prove2.me/theorems/06720602-b3f9-49eb-aeae-65b5ac13bd51
-- title:
--   Finite Format: p ne one of two le
-- statement:
--   `2 ≤ p` rules out `p = 1`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L303-L305
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L303-L305

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.p_ne_one_of_two_le {F : FiniteFormat} (hp : ((2 : ℕ) : Prec) ≤ F.p) :
    F.p ≠ ((1 : ℕ) : Prec) := by sorry
