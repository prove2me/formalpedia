-- Prove2me | Theorems.Thm_Mpfx_rnd_gt_mid_robust
-- name    : Mpfx.rnd_gt_mid_robust
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:03.007775+00:00
-- url     : https://prove2.me/theorems/4510f269-6998-4b80-b722-d1a8571b29da
-- title:
--   Mpfx: rnd gt mid robust
-- statement:
--   **Above-midpoint double rounding, crossing-robust** (Flocq
--   `round_round_gt_mid_further_place`).
--   Needs *no* away-from-top hypothesis: if the intermediate `z` stays in `x`'s
--   binade, binade consistency (`canonicalExp_eq_of_binade_top`) applies;
--   otherwise `z` crosses to `2^(mag x)`. In the crossing case `z` is the round-up of
--   `x`, bounded above by `2^(mag x) ∈ F₂`, so `z = 2^(mag x)` exactly — a value of
--   `F₁` — hence `◦₁(z) = z`, and `◦₁(x) = z` too since `x` is within `½·ulp₂` of it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L260-L318
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L260-L318

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
set_option autoImplicit true
open Mpfx

theorem Mpfx.rnd_gt_mid_robust {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : (rndUp F₁ x : ℝ) - ulp F₁ x / 2 + ulp F₂ x / 2 < x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by sorry
