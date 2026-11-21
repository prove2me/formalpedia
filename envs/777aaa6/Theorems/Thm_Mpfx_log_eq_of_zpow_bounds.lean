-- Prove2me | Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
-- name    : Mpfx.log_eq_of_zpow_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:18:12.696369+00:00
-- url     : https://prove2.me/theorems/f9df2b9f-3a27-4fd9-9f74-1f60888cc0bc
-- title:
--   Mpfx: log eq of zpow bounds
-- statement:
--   Read off `Int.log 2 x = k` from the binade bounds `2^k ≤ x < 2^(k+1)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L25-L31
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Utils.lean#L25-L31

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true
open Mpfx

theorem Mpfx.log_eq_of_zpow_bounds {x : ℝ} {k : ℤ} (hx : 0 < x)
    (hlo : (2 : ℝ) ^ k ≤ x) (hhi : x < (2 : ℝ) ^ (k + 1)) : Int.log 2 x = k := by sorry
