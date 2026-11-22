-- Prove2me | Theorems.Thm_Mpfx_ulp_pos
-- name    : Mpfx.ulp_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:44.756816+00:00
-- url     : https://prove2.me/theorems/b5f45fb6-0f3f-4e5e-af3e-055690cbf8fc
-- title:
--   Mpfx: ulp pos
-- statement:
--   The Mpfx construction uses the ulp pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L35-L36
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L35-L36

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.ulp_pos (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) : 0 < ulp F x := by sorry
