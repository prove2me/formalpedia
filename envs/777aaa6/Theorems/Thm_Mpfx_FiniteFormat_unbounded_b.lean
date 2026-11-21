-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
-- name    : Mpfx.FiniteFormat.unbounded_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:28.97922+00:00
-- url     : https://prove2.me/theorems/ff0b1523-0776-4764-aed9-9689332b8949
-- title:
--   Finite Format: unbounded b
-- statement:
--   The Finite Format construction uses the unbounded b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L401-L401
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L401-L401

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.unbounded_b (F : FiniteFormat) : F.unbounded.b = ⊤ := by sorry

attribute [defeq] Mpfx.FiniteFormat.unbounded_b
