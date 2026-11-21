-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_mono_toPositive
-- name    : Mpfx.RoundsFinite.mono_toPositive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:48.138092+00:00
-- url     : https://prove2.me/theorems/217b7409-1fd3-42c1-8d83-e7c686c68396
-- title:
--   Rounds Finite: mono to Positive
-- statement:
--   The Rounds Finite construction uses the mono to Positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L20-L23
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L20-L23

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.mono_toPositive {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic}
    (hx : x ≤ x') (hy : RoundsFinite F .toPositive x y)
    (hy' : RoundsFinite F .toPositive x' y') : (y : ℝ) ≤ y' := by sorry
