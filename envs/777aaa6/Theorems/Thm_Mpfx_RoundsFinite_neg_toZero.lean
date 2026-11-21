-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_neg_toZero
-- name    : Mpfx.RoundsFinite.neg_toZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:55:44.357781+00:00
-- url     : https://prove2.me/theorems/69d6f61a-814b-4bde-90b7-af8d5d6d7eaf
-- title:
--   Rounds Finite: neg to Zero
-- statement:
--   Sign-symmetry of `RoundsFinite` at mode `.toZero`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L64-L69
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L64-L69

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.neg_toZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .toZero x y ↔ RoundsFinite F .toZero (-x) (-y) := by sorry
