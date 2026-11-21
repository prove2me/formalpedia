-- Prove2me | Theorems.Thm_Mpfx_abs_floor_add_one_le_of_abs_lt
-- name    : Mpfx.abs_floor_add_one_le_of_abs_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:35.865722+00:00
-- url     : https://prove2.me/theorems/d6e80187-8b5b-41cd-a666-d01af46c2ea3
-- title:
--   Mpfx: abs floor add one le of abs lt
-- statement:
--   `|⌊r⌋ + 1| ≤ 2^p` when `|r| < 2^p`: the canonical bound for the ceiling
--   mantissa off the floor.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L134-L148
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L134-L148

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_floor_add_one_le_of_abs_lt {r : ℝ} {p : ℕ}
    (h : |r| < (2 : ℝ) ^ p) :
    |⌊r⌋ + 1| ≤ (2 : ℤ) ^ p := by sorry
