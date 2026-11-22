-- Prove2me | Theorems.Thm_Mpfx_rndDiv_expFinite
-- name    : Mpfx.rndDiv_expFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:54.010148+00:00
-- url     : https://prove2.me/theorems/10617ccb-d0fa-4632-9b5b-6cc1c80eadd9
-- title:
--   Mpfx: rnd Div exp Finite
-- statement:
--   **rnd-div, minimum quantum** (Roux Theorem 29, radix 2). With `exp = emin` formats
--   `F₁ = 𝒜(p₁, emin₁, b₁)` and `F₂ = 𝒜(p₂, emin₂, b₂)`, double rounding to nearest of
--   `a / b` (**arbitrary** `a, b ∈ F₁`, `b ≠ 0`) is innocuous — including underflowing
--   quotients — when
--
--   * **precision:** `p₂ ≥ 2·p₁`,
--   * **exponent:** the underflow bound `emin₂ ≤ emin₁ − p₁ − 2`,
--   * **bounds:** no relationship required (overflow-free `unbounded` roundings).
--
--   A precision + underflow *margin* (not exact containment — `a / b` is generally
--   non-representable). Matches Flocq's `round_round_div_FLT`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Div.lean#L541-L555
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Div.lean#L541-L555

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Div
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDiv_expFinite {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : QExp)) (hexp₂ : F₂.exp = (emin₂ : QExp))
    (hemin : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbne : (b : ℝ) ≠ 0)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by sorry
