-- Prove2me | Theorems.Thm_Mpfx_nearest_error_le_half_ulp
-- name    : Mpfx.nearest_error_le_half_ulp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:51.377294+00:00
-- url     : https://prove2.me/theorems/64b53644-7f70-46e9-baa0-db83d0aee477
-- title:
--   Mpfx: nearest error le half ulp
-- statement:
--   **Nearest error bound.** A round-to-nearest value `z` of `x` is within half
--   an ulp of `x`. Stated over `F.unbounded`, where the directed candidates always
--   exist.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L178-L192
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L178-L192

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.nearest_error_le_half_ulp {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {z : Dyadic} (h : RoundsFinite F.unbounded (.nearest tb) x z) :
    |(z : ℝ) - x| ≤ ulp F x / 2 := by sorry
