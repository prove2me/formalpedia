-- Prove2me | Theorems.Thm_Mpfx_not_isUndefined_of_two_le_p
-- name    : Mpfx.not_isUndefined_of_two_le_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:04.672559+00:00
-- url     : https://prove2.me/theorems/01232fa5-9520-4b87-b726-48f163c7a033
-- title:
--   Mpfx: not is Undefined of two le p
-- statement:
--   `2 ≤ F.p` rules out `IsUndefined` (which requires `p = 1`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L185-L190
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L185-L190

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.not_isUndefined_of_two_le_p {F : FiniteFormat} {rm : RoundingMode}
    (hp : ((2 : ℕ) : Prec) ≤ F.p) : ¬ F.IsUndefined rm := by sorry
