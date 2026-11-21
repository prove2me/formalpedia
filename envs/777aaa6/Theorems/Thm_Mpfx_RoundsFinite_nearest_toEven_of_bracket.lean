-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_nearest_toEven_of_bracket
-- name    : Mpfx.RoundsFinite.nearest_toEven_of_bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:31.946182+00:00
-- url     : https://prove2.me/theorems/f62e116d-5442-4f11-baac-eab7b6cb076c
-- title:
--   Rounds Finite: nearest to Even of bracket
-- statement:
--   **Nearest-even between the round-down and the round-up.** The nearer of the
--   round-down `d` and the round-up `u`, the even one on a tie, is the nearest-even
--   rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L336-L347
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L336-L347

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.nearest_toEven_of_bracket {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (hy : y = d ∨ y = u) (hclose : |x - (y : ℝ)| ≤ |x - (d : ℝ)| ∧ |x - (y : ℝ)| ≤ |x - (u : ℝ)|)
    (htie : |x - (d : ℝ)| = |x - (u : ℝ)| → d ≠ u →
      F.IsEven y) :
    RoundsFinite F (.nearest .toEven) x y := by sorry
