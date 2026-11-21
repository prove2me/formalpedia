-- Prove2me | Theorems.Thm_Mpfx_two_zpow_dbl
-- name    : Mpfx.two_zpow_dbl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:12.751552+00:00
-- url     : https://prove2.me/theorems/74efad17-8741-4d2e-bc20-913d751b85b0
-- title:
--   Mpfx: two zpow dbl
-- statement:
--   `2^a = 2 · 2^(a-1)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L56-L57
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L56-L57

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_zpow_dbl (a : ℤ) : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by sorry
