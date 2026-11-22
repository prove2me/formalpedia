-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_unique_awayZero
-- name    : Mpfx.RoundsFinite.unique_awayZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:55:51.967987+00:00
-- url     : https://prove2.me/theorems/3b9891e8-a37c-4f62-b748-d799537d4e79
-- title:
--   Rounds Finite: unique away Zero
-- statement:
--   Sign-mirror of `unique_toZero`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L251-L260
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L251-L260

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.unique_awayZero {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .awayZero x y₁) (h₂ : RoundsFinite F .awayZero x y₂) :
    y₁ = y₂ := by sorry
