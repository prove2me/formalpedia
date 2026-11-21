-- Prove2me | Theorems.Thm_Mpfx_rndDown_add_ulp_le
-- name    : Mpfx.rndDown_add_ulp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:49:06.616086+00:00
-- url     : https://prove2.me/theorems/33c0c65d-76ac-4cfe-8bed-def6315f1db9
-- title:
--   Mpfx: rnd Down add ulp le
-- statement:
--   Below its binade top, the round-down plus one step stays at most `2^(⌊log₂ x⌋+1)`:
--   the floor point's successor at the canonical exponent is still a multiple of the
--   step.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L84-L99
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L84-L99

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_add_ulp_le (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hle : F.canonicalExp x ≤ Int.log 2 x + 1) :
    (rndDown F x : ℝ) + ulp F x ≤ 2 ^ (Int.log 2 x + 1) := by sorry
