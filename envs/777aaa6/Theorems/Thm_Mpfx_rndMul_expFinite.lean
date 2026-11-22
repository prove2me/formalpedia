-- Prove2me | Theorems.Thm_Mpfx_rndMul_expFinite
-- name    : Mpfx.rndMul_expFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:04:18.442182+00:00
-- url     : https://prove2.me/theorems/4b0e3f4f-2579-4588-8f07-17bf6d46ca42
-- title:
--   Mpfx: rnd Mul exp Finite
-- statement:
--   **rnd-mult, minimum quantum** (Roux Thm 10, radix 2). With `exp = emin` formats
--   `F₁ = 𝒜(p₁, emin₁, b₁)` and `F₂ = 𝒜(p₂, emin₂, b₂)`, double rounding of `x · y`
--   (`x, y ∈ F₁`) is innocuous for **any** rounding modes when
--
--   * **precision:** `p₂ ≥ 2·p₁`,
--   * **exponent:** `emin₂ ≤ 2·emin₁`,
--   * **bounds:** no relationship required (overflow-free `unbounded` roundings).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Mul.lean#L74-L86
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Mul.lean#L74-L86

import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_Mul
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndMul_expFinite {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode} {p₁ p₂ : ℕ}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : QExp)) (hexp₂ : F₂.exp = (emin₂ : QExp))
    (hemin : emin₂ ≤ 2 * emin₁)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) :
    RoundsFinite F₁.unbounded rm₁ ((x * y : Dyadic) : ℝ) w := by sorry
