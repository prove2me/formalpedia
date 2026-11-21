-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_neg_awayZero
-- name    : Mpfx.RoundsFinite.neg_awayZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:55:46.577443+00:00
-- url     : https://prove2.me/theorems/0ad441d8-5af7-492d-a48d-c3ecfbe2fd23
-- title:
--   Rounds Finite: neg away Zero
-- statement:
--   Sign-symmetry of `RoundsFinite` at mode `.awayZero`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L81-L86
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L81-L86

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.neg_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .awayZero x y ↔ RoundsFinite F .awayZero (-x) (-y) := by sorry
