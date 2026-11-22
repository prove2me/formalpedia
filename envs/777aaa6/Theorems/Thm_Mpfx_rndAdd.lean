-- Prove2me | Theorems.Thm_Mpfx_rndAdd
-- name    : Mpfx.rndAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:02:55.323556+00:00
-- url     : https://prove2.me/theorems/752fe804-99fb-41b2-9e64-832626a1df4d
-- title:
--   Mpfx: rnd Add
-- statement:
--   **rnd-plus** (Roux Theorem 20, radix 2, **either exponent regime**). With
--   `F₁ = 𝒜(p₁, exp₁, b₁)` and `F₂ = 𝒜(p₂, exp₂, b₂)`, double rounding to nearest of
--   `x + y` for **arbitrary** `x, y ∈ F₁` is innocuous when
--
--   * **precision:** `p₂ ≥ 2·p₁ + 1`,
--   * **exponent:** `exp₂ ≤ exp₁` (subsumes `⊥ ≤ ⊥` and `emin₂ ≤ emin₁`),
--   * **bounds:** no relationship required (overflow-free `unbounded` roundings).
--
--   `exp₂ ≤ exp₁` is the *quantum half* of `F₁ ⊆ F₂` (`𝒜-Contains-Prec`): `F₂` is at
--   least as fine as `F₁`. Same-sign operands reduce to `rndAdd_nonneg` (both
--   nonpositive by joint negation); mixed signs are a subtraction handled by
--   `rndDiff`. Matches Flocq's `round_round_plus_FLX`/`round_round_plus_FLT`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Add.lean#L704-L738
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Add.lean#L704-L738

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Add
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndAdd {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by sorry
