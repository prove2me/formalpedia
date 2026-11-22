-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_mono_toNegative
-- name    : Mpfx.RoundsFinite.mono_toNegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:48.652455+00:00
-- url     : https://prove2.me/theorems/3b084c8d-e9a8-4b99-8659-076f1d81ca3d
-- title:
--   Rounds Finite: mono to Negative
-- statement:
--   The Rounds Finite construction uses the mono to Negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L15-L18
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L15-L18

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.mono_toNegative {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic}
    (hx : x ≤ x') (hy : RoundsFinite F .toNegative x y)
    (hy' : RoundsFinite F .toNegative x' y') : (y : ℝ) ≤ y' := by sorry
