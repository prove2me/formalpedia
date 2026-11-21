-- Prove2me | Theorems.Thm_Mpfx_abs_one_lt_two_pow
-- name    : Mpfx.abs_one_lt_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:17:53.247931+00:00
-- url     : https://prove2.me/theorems/4934caf9-243b-4ee0-afe9-1ab36262ca97
-- title:
--   Mpfx: abs one lt two pow
-- statement:
--   `|1| < 2^p` for any positive precision.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L80-L83
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L80-L83

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_one_lt_two_pow {p : ℕ} (hp : 0 < p) : |(1 : ℤ)| < 2 ^ p := by sorry
