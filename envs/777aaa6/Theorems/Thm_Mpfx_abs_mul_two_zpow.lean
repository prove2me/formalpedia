-- Prove2me | Theorems.Thm_Mpfx_abs_mul_two_zpow
-- name    : Mpfx.abs_mul_two_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:05.98519+00:00
-- url     : https://prove2.me/theorems/82d1b436-f65c-4120-b8f9-1b6d22a6dd37
-- title:
--   Mpfx: abs mul two zpow
-- statement:
--   `|c · 2^e| = |c| · 2^e` for `c : ℝ, e : ℤ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L14-L16
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L14-L16

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_mul_two_zpow (c : ℝ) (e : ℤ) :
    |c * (2 : ℝ) ^ e| = |c| * (2 : ℝ) ^ e := by sorry
