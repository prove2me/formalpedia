-- Prove2me | Theorems.Thm_Mpfx_round_round_mid_cases
-- name    : Mpfx.round_round_mid_cases
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:46:58.70543+00:00
-- url     : https://prove2.me/theorems/45dd4f8c-9c6e-4d70-af21-a590fef9005f
-- title:
--   Mpfx: round round mid cases
-- statement:
--   **Midpoint case dispatch** (Flocq `round_round_mid_cases`). For `0 < x` with
--   `F₂` strictly finer than `F₁` at `x` (`h21`) and `x` inside its binade (`hle`),
--   double rounding of `x` is innocuous *provided the near-midpoint case is handled*:
--   if `|x − midp₁ x| ≤ ½·ulp₂` the caller supplies `hcmid`; otherwise `x` sits more
--   than `½·ulp₂` below the midpoint (→ `rnd_lt_mid'`) or above it
--   (→ `rnd_gt_mid_robust`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L335-L358
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L335-L358

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
set_option autoImplicit true
open Mpfx

theorem Mpfx.round_round_mid_cases {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w)
    (hcmid : |x - midp F₁ x| ≤ ulp F₂ x / 2 →
      RoundsFinite F₁.unbounded (.nearest tb₁) x w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by sorry
