-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RN_finite
-- name    : Mpfx.roundsRTO_RN_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:52:36.052718+00:00
-- url     : https://prove2.me/theorems/129f0aa8-1284-458b-b615-3cb13cb00f09
-- title:
--   Mpfx: rounds RTO RN finite
-- statement:
--   **rnd-RTO-RN** (RNE and RNA) under the relaxed RN containment; `2 ≤ F₂.p`
--   follows unless `F₁` is trivial.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Nearest.lean#L140-L150
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Nearest.lean#L140-L150

import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Nearest
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RN_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by sorry
