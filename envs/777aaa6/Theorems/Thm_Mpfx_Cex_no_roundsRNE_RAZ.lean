-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRNE_RAZ
-- name    : Mpfx.Cex.no_roundsRNE_RAZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:18.242827+00:00
-- url     : https://prove2.me/theorems/9546c61c-3f31-490a-bec0-1809af40a14d
-- title:
--   Cex: no rounds RNE RAZ
-- statement:
--   **RNE → RAZ.** `x = a + δ`: the intermediate RNE rounds down onto `a`, which
--   RAZ fixes, but the direct RAZ reaches past `a`, to at most `b`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L244-L255
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L244-L255

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRNE_RAZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁ .awayZero := by sorry
