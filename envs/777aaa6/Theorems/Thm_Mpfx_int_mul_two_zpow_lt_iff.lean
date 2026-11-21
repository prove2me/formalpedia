-- Prove2me | Theorems.Thm_Mpfx_int_mul_two_zpow_lt_iff
-- name    : Mpfx.int_mul_two_zpow_lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:52.371884+00:00
-- url     : https://prove2.me/theorems/d5f80d8f-55b5-4744-959e-8f6f66aa4f9f
-- title:
--   Mpfx: int mul two zpow lt iff
-- statement:
--   Integer multiples of `2^k` compare as their coefficients.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L118-L120
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L118-L120

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.int_mul_two_zpow_lt_iff {a b k : ℤ} :
    (a : ℝ) * (2 : ℝ) ^ k < (b : ℝ) * (2 : ℝ) ^ k ↔ a < b := by sorry
