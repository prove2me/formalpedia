-- Prove2me | Theorems.Thm_Mpfx_rndMul_expBot
-- name    : Mpfx.rndMul_expBot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:04:15.722124+00:00
-- url     : https://prove2.me/theorems/ba814efb-bea7-45bb-9722-3b4e04661039
-- title:
--   Mpfx: rnd Mul exp Bot
-- statement:
--   **rnd-mult, no minimum quantum** (Roux Thm 10 / Figueroa, radix 2). With `exp = ⊥`
--   formats `F₁ = 𝒜(p₁, ⊥, b₁)` and `F₂ = 𝒜(p₂, ⊥, b₂)`, double rounding of a product `x · y`
--   (`x, y ∈ F₁`) is innocuous for **any** rounding modes when
--
--   * **precision:** `p₂ ≥ 2·p₁`,
--   * **exponent:** both `⊥` (no minimum quantum),
--   * **bounds:** no relationship required — the roundings are overflow-free (`unbounded`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Mul.lean#L57-L65
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Mul.lean#L57-L65

import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_Mul
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndMul_expBot {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) :
    RoundsFinite F₁.unbounded rm₁ ((x * y : Dyadic) : ℝ) w := by sorry
