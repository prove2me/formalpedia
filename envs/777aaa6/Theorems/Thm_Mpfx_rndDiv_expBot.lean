-- Prove2me | Theorems.Thm_Mpfx_rndDiv_expBot
-- name    : Mpfx.rndDiv_expBot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:04:00.549676+00:00
-- url     : https://prove2.me/theorems/8df65342-b0bd-4677-a1e0-7274aeec5895
-- title:
--   Mpfx: rnd Div exp Bot
-- statement:
--   **rnd-div, no minimum quantum** (Roux Theorem 29, radix 2). With `exp = ⊥` formats
--   `F₁ = 𝒜(p₁, ⊥, b₁)` and `F₂ = 𝒜(p₂, ⊥, b₂)`, double rounding to nearest of `a / b`
--   (**arbitrary** `a, b ∈ F₁`, `b ≠ 0`) is innocuous when
--
--   * **precision:** `p₂ ≥ 2·p₁`,
--   * **exponent:** both `⊥`,
--   * **bounds:** no relationship required (overflow-free `unbounded` roundings).
--
--   As with `√`, `a / b` is generally non-representable, so this is a precision
--   *margin* (with `2p₁` bits a quotient never lands near an `F₁`-midpoint), not exact
--   containment. Matches the generality of Flocq's `round_round_div_FLX`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Div.lean#L518-L528
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Div.lean#L518-L528

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Div
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDiv_expBot {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbne : (b : ℝ) ≠ 0)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by sorry
