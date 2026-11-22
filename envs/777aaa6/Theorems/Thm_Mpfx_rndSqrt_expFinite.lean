-- Prove2me | Theorems.Thm_Mpfx_rndSqrt_expFinite
-- name    : Mpfx.rndSqrt_expFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:04:42.858169+00:00
-- url     : https://prove2.me/theorems/5c07b21b-c7e0-41e2-9f55-fcd2c037d95d
-- title:
--   Mpfx: rnd Sqrt exp Finite
-- statement:
--   **rnd-sqrt, minimum quantum** (Roux Theorem 25, radix 2). With `exp = emin` formats
--   `F₁ = 𝒜(p₁, emin₁, b₁)` and `F₂ = 𝒜(p₂, emin₂, b₂)`, double rounding to nearest of
--   `√x` (`x ∈ F₁`, `0 ≤ x`) is innocuous when
--
--   * **precision:** `p₂ ≥ 2·p₁ + 2`,
--   * **exponent:** `emin₁ ≤ 0` and the Table-II underflow bound
--     `emin₂ ≤ emin₁ − p₁ − 2  ∨  2·emin₂ ≤ emin₁ − 4·p₁ − 2`,
--   * **bounds:** no relationship required (overflow-free `unbounded` roundings).
--
--   A precision + underflow *margin* (not exact containment — `√x` is generally
--   irrational).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Sqrt.lean#L283-L314
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Sqrt.lean#L283-L314

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Sqrt
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndSqrt_expFinite {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 2 ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : QExp)) (hexp₂ : F₂.exp = (emin₂ : QExp))
    (hemin1 : emin₁ ≤ 0)
    (hE : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2 ∨ 2 * emin₂ ≤ emin₁ - 4 * (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x : Dyadic} (hx : x ∈ F₁) (hxpos : 0 ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt (x : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt (x : ℝ)) w := by sorry
