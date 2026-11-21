-- Prove2me | Theorems.Thm_Mpfx_rnd_gt_mid
-- name    : Mpfx.rnd_gt_mid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:52.22434+00:00
-- url     : https://prove2.me/theorems/67f6ef58-2116-4706-9707-03af6b60241d
-- title:
--   Mpfx: rnd gt mid
-- statement:
--   **Above-midpoint double rounding** (mirror of `rnd_lt_mid`, given binade
--   consistency). If `x` sits more than `½·ulp₂` above its upper `F₁`-midpoint
--   `rndUp F₁ x − ½·ulp₁`, double rounding agrees (it rounds *up*). Proved by
--   applying `rnd_lt_mid` to `−x`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L235-L251
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L235-L251

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
set_option autoImplicit true
open Mpfx

theorem Mpfx.rnd_gt_mid {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : x ≠ 0)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hmid : (rndUp F₁ x : ℝ) - ulp F₁ x / 2 + ulp F₂ x / 2 < x)
    (hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by sorry
