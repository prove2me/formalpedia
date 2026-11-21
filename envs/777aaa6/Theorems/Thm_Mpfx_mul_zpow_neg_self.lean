-- Prove2me | Theorems.Thm_Mpfx_mul_zpow_neg_self
-- name    : Mpfx.mul_zpow_neg_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:17:57.786593+00:00
-- url     : https://prove2.me/theorems/1066d945-4914-4fad-a4db-9ec0d8c5c50c
-- title:
--   Mpfx: mul zpow neg self
-- statement:
--   The "rescale back" identity: `x · 2^(-e) · 2^e = x`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L127-L130
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L127-L130

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.mul_zpow_neg_self (x : ℝ) (e : ℤ) :
    x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = x := by sorry
