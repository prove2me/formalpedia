-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_nearest_awayZero_of_bracket
-- name    : Mpfx.RoundsFinite.nearest_awayZero_of_bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:10.375221+00:00
-- url     : https://prove2.me/theorems/6380a7b0-ebe0-4f1f-a0e1-c6d823d71871
-- title:
--   Rounds Finite: nearest away Zero of bracket
-- statement:
--   **Nearest-away between the round-down and the round-up.** The nearer of the
--   round-down `d` and the round-up `u`, the larger in magnitude on a tie, is the
--   nearest-away rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L352-L364
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L352-L364

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.nearest_awayZero_of_bracket {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (hy : y = d ∨ y = u) (hclose : |x - (y : ℝ)| ≤ |x - (d : ℝ)| ∧ |x - (y : ℝ)| ≤ |x - (u : ℝ)|)
    (htie : |x - (d : ℝ)| = |x - (u : ℝ)| → d ≠ u →
      |(d : ℝ)| ≤ |(y : ℝ)| ∧ |(u : ℝ)| ≤ |(y : ℝ)|) :
    RoundsFinite F (.nearest .awayZero) x y := by sorry
