-- Prove2me | Theorems.Thm_Mpfx_isAboveQuantum_of_rndDown_pos
-- name    : Mpfx.isAboveQuantum_of_rndDown_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:00:19.858926+00:00
-- url     : https://prove2.me/theorems/9b43c069-4ec4-42cd-b64e-efd49c33ac88
-- title:
--   Mpfx: is Above Quantum of rnd Down pos
-- statement:
--   Below `2 ^ canonicalExp x` the floor collapses to `0`, so a nonzero
--   round-down is exactly the above-quantum condition.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L328-L344
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L328-L344

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.isAboveQuantum_of_rndDown_pos (F : FiniteFormat) {x : ℝ}
    (h : 0 < ((rndDown F x : Dyadic) : ℝ)) : F.IsAboveQuantum x := by sorry
