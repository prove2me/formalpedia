-- Prove2me | Theorems.Thm_Mpfx_two_zpow_half
-- name    : Mpfx.two_zpow_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:10.385681+00:00
-- url     : https://prove2.me/theorems/20ad9f22-c1e0-4ad0-92a7-353aef4981e6
-- title:
--   Mpfx: two zpow half
-- statement:
--   `2^a / 2 = 2^(a-1)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L60-L61
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L60-L61

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_zpow_half (a : ℤ) : (2 : ℝ) ^ a / 2 = (2 : ℝ) ^ (a - 1) := by sorry
