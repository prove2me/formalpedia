-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_eq_of_log_eq
-- name    : Mpfx.canonicalExp_eq_of_log_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:38.48836+00:00
-- url     : https://prove2.me/theorems/79d51094-7e97-4b73-82dc-132f06456251
-- title:
--   Mpfx: canonical Exp eq of log eq
-- statement:
--   `canonicalExp` depends only on the binade `Int.log 2 |·|` (away from `0`):
--   equal logs give equal canonical exponents.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L462-L465
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L462-L465

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_eq_of_log_eq (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0)
    (h : Int.log 2 |y| = Int.log 2 |z|) : F.canonicalExp y = F.canonicalExp z := by sorry
