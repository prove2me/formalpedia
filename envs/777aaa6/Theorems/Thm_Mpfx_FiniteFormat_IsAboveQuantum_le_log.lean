-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_IsAboveQuantum_le_log
-- name    : Mpfx.FiniteFormat.IsAboveQuantum.le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:32.992444+00:00
-- url     : https://prove2.me/theorems/693de90f-2304-421c-a0ae-b48b87070ae6
-- title:
--   Is Above Quantum: le log
-- statement:
--   On the positive side the absolute value drops out.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L366-L369
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L366-L369

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.IsAboveQuantum.le_log {F : FiniteFormat} {x : ℝ} (h : F.IsAboveQuantum x)
    (hx : 0 < x) : F.canonicalExp x ≤ Int.log 2 x := by sorry
