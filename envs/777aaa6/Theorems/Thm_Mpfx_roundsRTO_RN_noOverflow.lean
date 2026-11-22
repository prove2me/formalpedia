-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RN_noOverflow
-- name    : Mpfx.roundsRTO_RN_noOverflow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:24.357874+00:00
-- url     : https://prove2.me/theorems/3a5163a3-68df-4c2e-a8e0-1e1081da2e69
-- title:
--   Mpfx: rounds RTO RN no Overflow
-- statement:
--   **rnd-RTO-RN**, no overflow: if the double rounding stays in bound, so does the
--   direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L619-L626
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L619-L626

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RN_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ (.nearest tb) (z : ℝ) w) :
    ¬ Overflows F₁ (.nearest tb) x := by sorry
