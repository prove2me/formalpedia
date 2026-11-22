-- Prove2me | Theorems.Thm_Mpfx_rndDiff
-- name    : Mpfx.rndDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:08.87317+00:00
-- url     : https://prove2.me/theorems/70e76b81-1178-4af9-9d3c-0d0d3b2f72d4
-- title:
--   Mpfx: rnd Diff
-- statement:
--   **rnd-difference, nonnegative operands** (Roux Theorem 20, radix 2). With
--   `F₁ = 𝒜(p₁, exp₁, b₁)` and `F₂ = 𝒜(p₂, exp₂, b₂)`, double rounding to nearest of
--   `a − b` (`a, b ∈ F₁`, `0 ≤ a`, `0 ≤ b`) is innocuous when
--
--   * **precision:** `p₂ ≥ 2·p₁ + 1`,
--   * **exponent:** `exp₂ ≤ exp₁` (covers `⊥ ≤ ⊥` and `emin₂ ≤ emin₁`),
--   * **bounds:** no relationship required (overflow-free `unbounded` roundings).
--
--   The exponent condition `exp₂ ≤ exp₁` is exactly the *quantum half* of `F₁ ⊆ F₂`
--   (`𝒜-Contains-Prec`): `F₂` is at least as fine as `F₁`. The `2p₁+1`-bit exact
--   difference is either `F₂`-representable (a zero operand or `a = b`, exact case)
--   or pinned by the midpoint argument.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Add.lean#L652-L690
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Add.lean#L652-L690

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Add
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDiff {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hann : 0 ≤ (a : ℝ)) (hbnn : 0 ≤ (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a - b : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a - b : Dyadic) : ℝ) w := by sorry
