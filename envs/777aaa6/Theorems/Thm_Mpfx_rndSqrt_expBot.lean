-- Prove2me | Theorems.Thm_Mpfx_rndSqrt_expBot
-- name    : Mpfx.rndSqrt_expBot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:04:31.856842+00:00
-- url     : https://prove2.me/theorems/e7f1e610-9221-4d6e-9278-702ad2bc256b
-- title:
--   Mpfx: rnd Sqrt exp Bot
-- statement:
--   **rnd-sqrt, no minimum quantum** (Roux Theorem 25, radix 2). With `exp = ⊥` formats
--   `F₁ = 𝒜(p₁, ⊥, b₁)` and `F₂ = 𝒜(p₂, ⊥, b₂)`, double rounding to nearest of `√x`
--   (`x ∈ F₁`, `0 ≤ x`) is innocuous when
--
--   * **precision:** `p₂ ≥ 2·p₁ + 2`,
--   * **exponent:** both `⊥`,
--   * **bounds:** no relationship required (overflow-free `unbounded` roundings).
--
--   Unlike `×`/`+`, `√x` is generally irrational, so this is a precision *margin*
--   (with `2p₁+2` bits `√x` never lands near an `F₁`-midpoint), not exact containment
--   of a result format.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Sqrt.lean#L246-L270
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Sqrt.lean#L246-L270

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Sqrt
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndSqrt_expBot {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 2 ≤ p₂)
    (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x : Dyadic} (hx : x ∈ F₁) (hxpos : 0 ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt (x : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt (x : ℝ)) w := by sorry
