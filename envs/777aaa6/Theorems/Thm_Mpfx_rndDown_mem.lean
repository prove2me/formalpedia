-- Prove2me | Theorems.Thm_Mpfx_rndDown_mem
-- name    : Mpfx.rndDown_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:51:30.426391+00:00
-- url     : https://prove2.me/theorems/ff24b231-e171-4339-b182-d088fb4280e2
-- title:
--   Mpfx: rnd Down mem
-- statement:
--   The Mpfx construction uses the rnd Down mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L58-L59
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L58-L59

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_mem (F : FiniteFormat) (x : ℝ) : rndDown F x ∈ F.unbounded := by sorry
