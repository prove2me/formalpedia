-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRNE_RTO
-- name    : Mpfx.Cex.no_roundsRNE_RTO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:26.843943+00:00
-- url     : https://prove2.me/theorems/d33603c4-c479-4b99-a43d-3ba0026c1337
-- title:
--   Cex: no rounds RNE RTO
-- statement:
--   **RNE → RTO.** `x = h − δ`: the intermediate RNE lands exactly on the
--   non-odd `h`, which RTO fixes, but the direct RTO is inexact and so odd.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L275-L285
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L275-L285

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRNE_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁.toFiniteFormat .toOdd := by sorry
