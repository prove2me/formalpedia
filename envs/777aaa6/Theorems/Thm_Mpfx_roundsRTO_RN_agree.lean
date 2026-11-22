-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RN_agree
-- name    : Mpfx.roundsRTO_RN_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:52.468308+00:00
-- url     : https://prove2.me/theorems/cc1d7bae-67c1-4d7f-804a-c2f3d310aee2
-- title:
--   Mpfx: rounds RTO RN agree
-- statement:
--   **rnd-RTO-RN**, in bound: the double rounding agrees with the direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L687-L693
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L687-L693

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RN_agree {F₁ F₂ : FiniteFormat} {tb : TieBreak}
    (hsub : (F₁.extend 2).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ (.nearest tb) (z : ℝ) w)
    (hy : RoundsInBound F₁ (.nearest tb) x y) : w = y := by sorry
