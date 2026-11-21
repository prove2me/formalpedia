-- Prove2me | Theorems.Thm_Mpfx_ulp_of_ne_zero
-- name    : Mpfx.ulp_of_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:45.477327+00:00
-- url     : https://prove2.me/theorems/3253b999-f2ac-4c2d-ab71-1cfadcd4dd34
-- title:
--   Mpfx: ulp of ne zero
-- statement:
--   The Mpfx construction uses the ulp of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L28-L30
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L28-L30

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.ulp_of_ne_zero (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x := by sorry
