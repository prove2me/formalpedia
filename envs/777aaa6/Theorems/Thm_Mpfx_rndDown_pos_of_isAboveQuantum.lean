-- Prove2me | Theorems.Thm_Mpfx_rndDown_pos_of_isAboveQuantum
-- name    : Mpfx.rndDown_pos_of_isAboveQuantum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:57.756466+00:00
-- url     : https://prove2.me/theorems/622ad922-aae9-404e-897c-fdf1bdcf0e8f
-- title:
--   Mpfx: rnd Down pos of is Above Quantum
-- statement:
--   The Mpfx construction uses the rnd Down pos of is Above Quantum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L322-L324
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L322-L324

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_pos_of_isAboveQuantum (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hq : F.IsAboveQuantum x) : 0 < ((rndDown F x : Dyadic) : ℝ) := by sorry
