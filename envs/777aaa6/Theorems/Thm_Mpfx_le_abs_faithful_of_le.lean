-- Prove2me | Theorems.Thm_Mpfx_le_abs_faithful_of_le
-- name    : Mpfx.le_abs_faithful_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:44:04.675542+00:00
-- url     : https://prove2.me/theorems/4cd49c62-f98d-420f-8096-4e8564926a0a
-- title:
--   Mpfx: le abs faithful of le
-- statement:
--   Dual of `abs_faithful_le_of_le`: a nonnegative `N ∈ F` with `N ≤ |x|`
--   bounds a faithful rounding of `x` from below in magnitude.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L712-L726
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L712-L726

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.le_abs_faithful_of_le {F : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F) (hN_nn : 0 ≤ (N : ℝ)) (hxN : (N : ℝ) ≤ |x|)
    (hf : IsFaithfulRound F x z) : (N : ℝ) ≤ |(z : ℝ)| := by sorry
