-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRTZ_RTO
-- name    : Mpfx.Cex.no_roundsRTZ_RTO
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:29.309929+00:00
-- url     : https://prove2.me/theorems/2575d444-621c-4b98-b51f-83e30d5d0ebb
-- title:
--   Cex: no rounds RTZ RTO
-- statement:
--   **RTZ → RTO.** `x = h + δ` above a positive non-odd value `h` with a value
--   `c > h` above it: the intermediate RTZ truncates onto `h`, which RTO fixes, but
--   the direct RTO is inexact and so odd, at most `c`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L290-L305
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L290-L305

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRTZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 3)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁.toFiniteFormat .toOdd := by sorry
