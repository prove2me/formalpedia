-- Prove2me | Theorems.Thm_Mpfx_lt_rndDown_add_ulp
-- name    : Mpfx.lt_rndDown_add_ulp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:56:55.92118+00:00
-- url     : https://prove2.me/theorems/f1bdfe05-3481-4317-bb66-03e874454d20
-- title:
--   Mpfx: lt rnd Down add ulp
-- statement:
--   The Mpfx construction uses the lt rnd Down add ulp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L65-L79
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L65-L79

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.lt_rndDown_add_ulp (F : FiniteFormat) {x : ℝ}
    (hx : ¬(x = 0 ∧ F.exp = ⊥)) :
    x < (rndDown F x : ℝ) + ulp F x := by sorry
