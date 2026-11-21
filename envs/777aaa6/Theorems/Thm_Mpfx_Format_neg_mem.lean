-- Prove2me | Theorems.Thm_Mpfx_Format_neg_mem
-- name    : Mpfx.Format.neg_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:24:58.380075+00:00
-- url     : https://prove2.me/theorems/31bf8fb1-a7d3-43d4-9e60-807c92c3de62
-- title:
--   Format: neg mem
-- statement:
--   Format membership is closed under negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L147-L149
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L147-L149

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.neg_mem {F : Format} {d : Dyadic} (h : d ∈ F) : (-d) ∈ F := by sorry
