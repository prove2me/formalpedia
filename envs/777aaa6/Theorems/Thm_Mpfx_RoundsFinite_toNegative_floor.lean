-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor
-- name    : Mpfx.RoundsFinite.toNegative_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:53.085511+00:00
-- url     : https://prove2.me/theorems/6ac22555-99ea-45e8-9233-ccb4065d4599
-- title:
--   Rounds Finite: to Negative floor
-- statement:
--   The floor point at the canonical exponent **is** the round-down.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L433-L453
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L433-L453

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toNegative_floor (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toNegative x
      (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x)) := by sorry
