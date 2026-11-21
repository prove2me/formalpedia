-- Prove2me | Theorems.Thm_Mpfx_abs_floor_le_of_abs_lt
-- name    : Mpfx.abs_floor_le_of_abs_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:16.949177+00:00
-- url     : https://prove2.me/theorems/67468038-4c1d-437b-9c41-5036cb324133
-- title:
--   Mpfx: abs floor le of abs lt
-- statement:
--   For `r` with `|r| < N`, the floor `⌊r⌋` has `|⌊r⌋| ≤ N`. The
--   asymmetry: negative floors can saturate (e.g. `⌊-1.5⌋ = -2` with
--   `|-1.5| < 2` but `|⌊-1.5⌋| = 2`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L103-L115
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L103-L115

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_floor_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
    |⌊r⌋| ≤ N := by sorry
