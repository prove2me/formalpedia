-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_log_sub_p_le_canonicalExp
-- name    : Mpfx.FiniteFormat.log_sub_p_le_canonicalExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:40.134949+00:00
-- url     : https://prove2.me/theorems/e415f140-5d93-4bdf-a288-fd118cc18f2b
-- title:
--   Finite Format: log sub p le canonical Exp
-- statement:
--   The canonical exponent dominates `Int.log 2 |x| + 1 - p` whenever
--   `F.p` is finite and `x ≠ 0`. Needed to bound `|⌊x · 2^(-e)⌋| ≤ 2^p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L348-L354
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L348-L354

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.log_sub_p_le_canonicalExp (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0)
    {p : ℕ} (hp : F.p = (p : Prec)) :
    Int.log 2 |x| + 1 - (p : ℤ) ≤ F.canonicalExp x := by sorry
