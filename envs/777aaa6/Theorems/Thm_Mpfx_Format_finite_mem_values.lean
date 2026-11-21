-- Prove2me | Theorems.Thm_Mpfx_Format_finite_mem_values
-- name    : Mpfx.Format.finite_mem_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:03.01978+00:00
-- url     : https://prove2.me/theorems/34dfdbcd-e0b4-4bf6-9723-cc241ec0bfd7
-- title:
--   Format: finite mem values
-- statement:
--   The Format construction uses the finite mem values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L115-L116
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L115-L116

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.Format.finite_mem_values {F : Format} {d : Dyadic} :
    WithSpecial.finite d ∈ F.values ↔ d ∈ F := by sorry
