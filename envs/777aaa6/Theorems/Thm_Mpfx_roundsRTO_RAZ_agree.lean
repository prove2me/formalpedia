-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RAZ_agree
-- name    : Mpfx.roundsRTO_RAZ_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:53.389802+00:00
-- url     : https://prove2.me/theorems/e21de42d-dc44-4fa8-8927-97bd844bceb4
-- title:
--   Mpfx: rounds RTO RAZ agree
-- statement:
--   **rnd-RTO-RAZ**, in bound: the double rounding agrees with the direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L678-L684
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L678-L684

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RAZ_agree {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) (hy : RoundsInBound F₁ .awayZero x y) :
    w = y := by sorry
