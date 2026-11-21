-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RN_finite_of_extend
-- name    : Mpfx.roundsRTO_RN_finite_of_extend
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:47:21.557447+00:00
-- url     : https://prove2.me/theorems/0b4733bb-2ff8-46ae-8fa6-cad88be755c8
-- title:
--   Mpfx: rounds RTO RN finite of extend
-- statement:
--   **rnd-RTO-RN** under `F₁.extend 2 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
--   bound.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Nearest.lean#L94-L136
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Nearest.lean#L94-L136

import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Nearest
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RN_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub2 : (F₁.extend 2).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by sorry
