-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRAZ_RTZ
-- name    : Mpfx.Cex.no_roundsRAZ_RTZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:16.526838+00:00
-- url     : https://prove2.me/theorems/4416104b-0436-4f9f-b901-f84bf35ebf71
-- title:
--   Cex: no rounds RAZ RTZ
-- statement:
--   **RAZ → RTZ.** `x = a − δ`: the intermediate RAZ pushes `x` up onto `a`,
--   which RTZ fixes, but the direct RTZ falls below `a`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L214-L223
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L214-L223

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRAZ_RTZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .awayZero F₁ .toZero := by sorry
