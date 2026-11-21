-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_neg_mem
-- name    : Mpfx.FiniteFormat.neg_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:17.395293+00:00
-- url     : https://prove2.me/theorems/b3c89a11-1d88-437b-9e12-bb1a4439a318
-- title:
--   Finite Format: neg mem
-- statement:
--   (Finite-)format membership is closed under negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L282-L283
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L282-L283

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.neg_mem {F : FiniteFormat} {d : Dyadic} (h : d ∈ F) : (-d) ∈ F := by sorry
