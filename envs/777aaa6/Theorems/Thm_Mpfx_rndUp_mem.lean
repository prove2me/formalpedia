-- Prove2me | Theorems.Thm_Mpfx_rndUp_mem
-- name    : Mpfx.rndUp_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:05.532283+00:00
-- url     : https://prove2.me/theorems/c1bfce72-0df7-4c80-8f8e-fcfee2768f8b
-- title:
--   Mpfx: rnd Up mem
-- statement:
--   The Mpfx construction uses the rnd Up mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L128-L129
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L128-L129

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndUp_mem (F : FiniteFormat) (x : ℝ) : rndUp F x ∈ F.unbounded := by sorry
