-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
-- name    : Mpfx.FiniteFormat.exp_le_canonicalExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:12.909338+00:00
-- url     : https://prove2.me/theorems/9f72853a-77f5-4116-8cce-a2403519ceb0
-- title:
--   Finite Format: exp le canonical Exp
-- statement:
--   The canonical exponent dominates `F.exp` whenever `F.exp` is finite.
--   Needed to discharge `quantumAtLeast F.exp` for the rounded value.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L334-L344
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L334-L344

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.exp_le_canonicalExp (F : FiniteFormat) (x : ℝ)
    {e' : ℤ} (hexp : F.exp = (e' : QExp)) :
    e' ≤ F.canonicalExp x := by sorry
