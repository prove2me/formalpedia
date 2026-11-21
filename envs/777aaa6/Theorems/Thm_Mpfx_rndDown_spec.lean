-- Prove2me | Theorems.Thm_Mpfx_rndDown_spec
-- name    : Mpfx.rndDown_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:47.584752+00:00
-- url     : https://prove2.me/theorems/0d90b36a-f4b5-46cd-85fa-cc678f55bc6b
-- title:
--   Mpfx: rnd Down spec
-- statement:
--   The Mpfx construction uses the rnd Down spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L51-L53
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L51-L53

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_spec (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toNegative x (rndDown F x) := by sorry
