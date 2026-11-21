-- Prove2me | Theorems.Thm_Mpfx_mul_nonneg_of_common_sign
-- name    : Mpfx.mul_nonneg_of_common_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:25.916437+00:00
-- url     : https://prove2.me/theorems/66f384e5-c6be-4048-81d5-5b6c6663f5f3
-- title:
--   Mpfx: mul nonneg of common sign
-- statement:
--   Sign-transitivity through a nonzero pivot: if `y·x ≥ 0` and `z·x ≥ 0`,
--   and `x = 0` implies `y = 0`, then `y·z ≥ 0`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L87-L93
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L87-L93

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.mul_nonneg_of_common_sign {x : ℝ} {y z : ℝ}
    (hyx : y * x ≥ 0) (hzx : z * x ≥ 0) (hy0 : x = 0 → y = 0) :
    y * z ≥ 0 := by sorry
