-- Prove2me | Theorems.Thm_Mpfx_rnd_lt_mid
-- name    : Mpfx.rnd_lt_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:53:26.831287+00:00
-- url     : https://prove2.me/theorems/45026e1a-29f9-40ad-9f53-5b2068bf03b5
-- title:
--   Mpfx: rnd lt mid
-- statement:
--   **Lemma 16 (with binade consistency).** For `0 < x` sitting more than
--   `½·ulp₂` below its `F₁`-midpoint, with `F₂`'s canonical exponent strictly finer
--   than `F₁`'s and the intermediate nearest rounding `z` staying in `x`'s
--   `F₁`-binade (`hcexp`), a nearest rounding in `F₂` then in `F₁` agrees with the
--   direct `F₁` nearest rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L32-L129
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L32-L129

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
set_option autoImplicit true
open Mpfx

theorem Mpfx.rnd_lt_mid {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : x ≠ 0)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    (hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by sorry
