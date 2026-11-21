-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_zero_mem
-- name    : Mpfx.FiniteFormat.zero_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:24:59.825927+00:00
-- url     : https://prove2.me/theorems/29b32064-03be-4606-b5ba-538832fd9ab0
-- title:
--   Finite Format: zero mem
-- statement:
--   Zero is in every (finite) format.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L279-L279
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L279-L279

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.zero_mem (F : FiniteFormat) : (0 : Dyadic) ∈ F := by sorry
