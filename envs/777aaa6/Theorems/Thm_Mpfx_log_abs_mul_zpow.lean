-- Prove2me | Theorems.Thm_Mpfx_log_abs_mul_zpow
-- name    : Mpfx.log_abs_mul_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:17:59.829808+00:00
-- url     : https://prove2.me/theorems/5dc96ce5-1daf-48b7-a8ee-b2dc292fd97c
-- title:
--   Mpfx: log abs mul zpow
-- statement:
--   `Int.log 2 |k · 2^e'| = Int.log 2 |k| + e'` for nonzero integer `k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L34-L44
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L34-L44

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.log_abs_mul_zpow {k : ℤ} (hk_ne : k ≠ 0) (e' : ℤ) :
    Int.log 2 |(k : ℝ) * (2 : ℝ) ^ e'| = Int.log 2 (|k| : ℝ) + e' := by sorry
