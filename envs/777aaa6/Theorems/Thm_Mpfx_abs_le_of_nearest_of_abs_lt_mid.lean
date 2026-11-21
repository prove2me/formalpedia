-- Prove2me | Theorems.Thm_Mpfx_abs_le_of_nearest_of_abs_lt_mid
-- name    : Mpfx.abs_le_of_nearest_of_abs_lt_mid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:53:25.797971+00:00
-- url     : https://prove2.me/theorems/5d333271-f2cf-4fbc-8bc4-c7fe571291b1
-- title:
--   Mpfx: abs le of nearest of abs lt mid
-- statement:
--   An input strictly within the midpoint has its nearest rounding within `d`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L279-L289
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L279-L289

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_le_of_nearest_of_abs_lt_mid {F : FiniteFormat} {d : Dyadic}
    (hd : d ∈ F.unbounded) (hd0 : 0 ≤ (d : ℝ)) (hguard : F.exp = ⊥ → 0 < (d : ℝ))
    {tb : TieBreak} {x : ℝ} {y : Dyadic} (hy : RoundsFinite F.unbounded (.nearest tb) x y)
    (hxM : |x| < ((F.extend 1).toFormat.next d : ℝ)) : |(y : ℝ)| ≤ d := by sorry
