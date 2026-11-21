-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil
-- name    : Mpfx.RoundsFinite.toPositive_ceil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:43:49.609685+00:00
-- url     : https://prove2.me/theorems/540cd27e-5cc5-4c99-b193-86e07db09de8
-- title:
--   Rounds Finite: to Positive ceil
-- statement:
--   The ceiling point at the canonical exponent **is** the round-up.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L456-L463
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L456-L463

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toPositive_ceil (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toPositive x
      (Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x)) := by sorry
