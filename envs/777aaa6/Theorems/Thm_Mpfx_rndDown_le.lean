-- Prove2me | Theorems.Thm_Mpfx_rndDown_le
-- name    : Mpfx.rndDown_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:45:52.526107+00:00
-- url     : https://prove2.me/theorems/3b49d7b3-7073-4843-8b06-ccb732bdc3d9
-- title:
--   Mpfx: rnd Down le
-- statement:
--   The Mpfx construction uses the rnd Down le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L55-L56
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L55-L56

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_le (F : FiniteFormat) (x : ℝ) : (rndDown F x : ℝ) ≤ x := by sorry
