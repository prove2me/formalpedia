-- Prove2me | Theorems.Thm_Mpfx_abs_le_mid_of_nearest
-- name    : Mpfx.abs_le_mid_of_nearest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:53:02.280383+00:00
-- url     : https://prove2.me/theorems/ede52ce4-092d-439b-8f4c-7516deb29b2c
-- title:
--   Mpfx: abs le mid of nearest
-- statement:
--   An input whose nearest rounding is within `d` is within the midpoint.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L265-L276
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L265-L276

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_le_mid_of_nearest {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F.unbounded)
    (hd0 : 0 ≤ (d : ℝ)) (hguard : F.exp = ⊥ → 0 < (d : ℝ)) {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (hy : RoundsFinite F.unbounded (.nearest tb) x y) (hyd : |(y : ℝ)| ≤ d) :
    |x| ≤ ((F.extend 1).toFormat.next d : ℝ) := by sorry
