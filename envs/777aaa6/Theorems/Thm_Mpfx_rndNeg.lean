-- Prove2me | Theorems.Thm_Mpfx_rndNeg
-- name    : Mpfx.rndNeg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:46:44.960943+00:00
-- url     : https://prove2.me/theorems/f3c9a34f-9781-40d0-b8dd-9ed7aa1dbb61
-- title:
--   Mpfx: rnd Neg
-- statement:
--   **Double-rounding negation transport.** Both roundings being to-nearest,
--   double rounding commutes with negation: to double-round `v` it suffices to
--   double-round `-v` with the negated intermediate and result `(-z, -w)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L218-L229
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L218-L229

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndNeg {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {v : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) v z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w)
    (hbase : RoundsFinite F₂.unbounded (.nearest tb₂) (-v) (-z) →
      RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) →
      RoundsFinite F₁.unbounded (.nearest tb₁) (-v) (-w)) :
    RoundsFinite F₁.unbounded (.nearest tb₁) v w := by sorry
