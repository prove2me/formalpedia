-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_mem_neg_iff
-- name    : Mpfx.FiniteFormat.mem_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:39.151183+00:00
-- url     : https://prove2.me/theorems/cf1864df-02c0-4b6e-9079-fc905fe96c43
-- title:
--   Finite Format: mem neg iff
-- statement:
--   The Finite Format construction uses the mem neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L285-L286
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L285-L286

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.mem_neg_iff (F : FiniteFormat) (d : Dyadic) : (-d) ∈ F ↔ d ∈ F := by sorry
