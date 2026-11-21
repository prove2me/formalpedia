-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_forall_mem_congr_neg
-- name    : Mpfx.FiniteFormat.forall_mem_congr_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:16.618337+00:00
-- url     : https://prove2.me/theorems/d2ba6ead-59a3-484b-9ba3-019f363dabb5
-- title:
--   Finite Format: forall mem congr neg
-- statement:
--   Quantifying over `F` is quantifying over its negations: two predicates that
--   agree up to negation hold for all of `F` together.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L290-L293
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L290-L293

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.forall_mem_congr_neg (F : FiniteFormat) {P Q : Dyadic → Prop}
    (h : ∀ z, P z ↔ Q (-z)) : (∀ z, z ∈ F → P z) ↔ ∀ z, z ∈ F → Q z := by sorry
