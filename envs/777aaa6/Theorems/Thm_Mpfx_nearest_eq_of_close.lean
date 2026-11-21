-- Prove2me | Theorems.Thm_Mpfx_nearest_eq_of_close
-- name    : Mpfx.nearest_eq_of_close
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:46:34.953833+00:00
-- url     : https://prove2.me/theorems/738b38f3-7d86-4f7c-8dce-5cbe4d3e6862
-- title:
--   Mpfx: nearest eq of close
-- statement:
--   **Nearest of a value close to a multiple of the step.** If `v`'s scaled mantissa
--   is within `½` of an integer `m`, then `m · 2^(canonicalExp v)` is the
--   nearest rounding of `v` (either tie-break), whichever side of `m` the scaled
--   mantissa falls on.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L198-L224
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L198-L224

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.nearest_eq_of_close (F : FiniteFormat) (tb : TieBreak) (v : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) {m : ℤ}
    (h : |v * (2 : ℝ) ^ (-(F.canonicalExp v)) - (m : ℝ)| < 1 / 2) :
    RoundsFinite F.unbounded (.nearest tb) v (Dyadic.ofIntZpow m (F.canonicalExp v)) := by sorry
