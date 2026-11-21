-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRAZ_RTO
-- name    : Mpfx.Cex.no_roundsRAZ_RTO
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:32.408641+00:00
-- url     : https://prove2.me/theorems/33288f4b-c29a-408e-aa2a-c849d45b427a
-- title:
--   Cex: no rounds RAZ RTO
-- statement:
--   **RAZ → RTO.** `x = h − δ` below a positive value `h` that is not odd: the
--   intermediate RAZ lands exactly on `h`, which RTO fixes, but the direct RTO is
--   inexact and so odd.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L260-L271
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L260-L271

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRAZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .awayZero F₁.toFiniteFormat .toOdd := by sorry
