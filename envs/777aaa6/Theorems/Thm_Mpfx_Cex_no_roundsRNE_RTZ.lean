-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRNE_RTZ
-- name    : Mpfx.Cex.no_roundsRNE_RTZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:06.781333+00:00
-- url     : https://prove2.me/theorems/1dee6499-4397-4e4f-9593-c1e2ead2dfaa
-- title:
--   Cex: no rounds RNE RTZ
-- statement:
--   **RNE → RTZ.** `x = a − δ` below a positive value `a`: the intermediate RNE
--   carries `x` up onto `a`, which RTZ fixes, but the direct RTZ falls below
--   `a`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L202-L210
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L202-L210

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRNE_RTZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁ .toZero := by sorry
