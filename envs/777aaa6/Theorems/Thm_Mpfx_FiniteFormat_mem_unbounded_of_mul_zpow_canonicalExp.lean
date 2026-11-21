-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_mem_unbounded_of_mul_zpow_canonicalExp
-- name    : Mpfx.FiniteFormat.mem_unbounded_of_mul_zpow_canonicalExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:53.906322+00:00
-- url     : https://prove2.me/theorems/fa3de296-5076-48a0-a0d9-e6de6540dbdd
-- title:
--   Finite Format: mem unbounded of mul zpow canonical Exp
-- statement:
--   Conversely, a multiple of `2^canonicalExp x` is a value of `F`: the step
--   meets the minimum quantum, and the coefficient fits the precision.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L544-L560
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L544-L560

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.FiniteFormat.mem_unbounded_of_mul_zpow_canonicalExp (F : FiniteFormat) {x : Dyadic}
    {m : ℤ} (h : (x : ℝ) = m * (2 : ℝ) ^ F.canonicalExp x) : x ∈ F.unbounded := by sorry
