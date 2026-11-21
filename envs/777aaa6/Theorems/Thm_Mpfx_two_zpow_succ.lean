-- Prove2me | Theorems.Thm_Mpfx_two_zpow_succ
-- name    : Mpfx.two_zpow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:37.23767+00:00
-- url     : https://prove2.me/theorems/149410ad-de17-495e-a0cd-0ce2e4c8a031
-- title:
--   Mpfx: two zpow succ
-- statement:
--   `2^(t+1) = 2 · 2^t`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L52-L53
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L52-L53

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_zpow_succ (t : ℤ) : (2 : ℝ) ^ (t + 1) = 2 * (2 : ℝ) ^ t := by sorry
