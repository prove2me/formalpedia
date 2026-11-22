-- Prove2me | Theorems.Thm_Mpfx_rndDown_max
-- name    : Mpfx.rndDown_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:47.704505+00:00
-- url     : https://prove2.me/theorems/c8fabc28-7610-44f1-ac0c-4905ee04d3fb
-- title:
--   Mpfx: rnd Down max
-- statement:
--   The Mpfx construction uses the rnd Down max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L61-L63
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L61-L63

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_max (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz : z ∈ F.unbounded) (hzx : (z : ℝ) ≤ x) : (z : ℝ) ≤ (rndDown F x : ℝ) := by sorry
