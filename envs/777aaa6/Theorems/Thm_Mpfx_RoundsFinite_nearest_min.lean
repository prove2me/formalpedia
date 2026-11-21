-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_nearest_min
-- name    : Mpfx.RoundsFinite.nearest_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:44:03.520984+00:00
-- url     : https://prove2.me/theorems/d67e8785-1e66-4211-8eca-a1e8bab1c273
-- title:
--   Rounds Finite: nearest min
-- statement:
--   The nearest-minimality conjunct, uniform in the tie-break: both cases carry
--   it in the same position, but the mode `match` needs `tb` to reduce.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L730-L736
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L730-L736

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.nearest_min {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F (.nearest tb) x y) {z : Dyadic}
    (hz : z ∈ F) (hzf : IsFaithfulRound F x z) :
    |x - (y : ℝ)| ≤ |x - (z : ℝ)| := by sorry
