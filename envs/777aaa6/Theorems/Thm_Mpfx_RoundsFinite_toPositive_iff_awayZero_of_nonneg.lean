-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg
-- name    : Mpfx.RoundsFinite.toPositive_iff_awayZero_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:33.836146+00:00
-- url     : https://prove2.me/theorems/bf81ee73-6cf5-4d09-9059-c603db107261
-- title:
--   Rounds Finite: to Positive iff away Zero of nonneg
-- statement:
--   The Rounds Finite construction uses the to Positive iff away Zero of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L124-L156
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L124-L156

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toPositive_iff_awayZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .awayZero x y := by sorry
