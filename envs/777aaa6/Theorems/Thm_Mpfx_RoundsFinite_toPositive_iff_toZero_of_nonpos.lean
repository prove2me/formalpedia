-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_toZero_of_nonpos
-- name    : Mpfx.RoundsFinite.toPositive_iff_toZero_of_nonpos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:44:07.128639+00:00
-- url     : https://prove2.me/theorems/e005ba4b-f378-4850-a1f3-b4f979e4cdbd
-- title:
--   Rounds Finite: to Positive iff to Zero of nonpos
-- statement:
--   The Rounds Finite construction uses the to Positive iff to Zero of nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L158-L192
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L158-L192

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toPositive_iff_toZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .toZero x y := by sorry
