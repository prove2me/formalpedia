-- Prove2me | Theorems.Thm_Mpfx_ne_zero_of_not_boundOK
-- name    : Mpfx.ne_zero_of_not_boundOK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:18.810802+00:00
-- url     : https://prove2.me/theorems/298f2ee1-ea16-41df-80c3-b1e08e143ae7
-- title:
--   Mpfx: ne zero of not bound OK
-- statement:
--   An out-of-bound value is nonzero.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L23-L25
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L23-L25

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.ne_zero_of_not_boundOK {F : FiniteFormat} {y : Dyadic}
    (h : ¬ Format.boundOK F.b y) : (y : ℝ) ≠ 0 := by sorry
