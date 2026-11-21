-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isAboveQuantum_of_le_log
-- name    : Mpfx.FiniteFormat.isAboveQuantum_of_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:44.675719+00:00
-- url     : https://prove2.me/theorems/9496ec1c-33dc-4f04-888f-2c2600fb9ec0
-- title:
--   Finite Format: is Above Quantum of le log
-- statement:
--   The Finite Format construction uses the is Above Quantum of le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L371-L374
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L371-L374

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isAboveQuantum_of_le_log {F : FiniteFormat} {x : ℝ} (hx : 0 < x)
    (h : F.canonicalExp x ≤ Int.log 2 x) : F.IsAboveQuantum x := by sorry
