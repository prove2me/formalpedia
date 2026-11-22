-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRTZ_RAZ
-- name    : Mpfx.Cex.no_roundsRTZ_RAZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:22.344191+00:00
-- url     : https://prove2.me/theorems/471a1dd6-7b53-434b-82bc-757a2aca7712
-- title:
--   Cex: no rounds RTZ RAZ
-- statement:
--   **RTZ → RAZ.** `x = a + δ` above the smaller of two positive values
--   `a < b`: the intermediate RTZ truncates onto `a`, which RAZ fixes, but the
--   direct RAZ reaches past `a`, to at most `b`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L228-L240
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L228-L240

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRTZ_RAZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁ .awayZero := by sorry
