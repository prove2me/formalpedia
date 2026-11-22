-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRTZ_RNE
-- name    : Mpfx.Cex.no_roundsRTZ_RNE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:29.759193+00:00
-- url     : https://prove2.me/theorems/5b28a2cd-9369-429c-aab8-2012d210366b
-- title:
--   Cex: no rounds RTZ RNE
-- statement:
--   **RTZ → RNE.** Adjacent values `u < u'` with `u ≥ 0` even, and
--   `x = m + δ` just above their midpoint `m`: the intermediate RTZ lands in
--   `[u, m]`, where RNE returns `u` (at `m` by the tie-break), but the direct RNE
--   returns the strictly nearer `u'`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L311-L345
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L311-L345

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRTZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁.toFiniteFormat (.nearest .toEven) := by sorry
