-- Prove2me | Theorems.Thm_Mpfx_nearest_eq_rndDown_of_lt_midp
-- name    : Mpfx.nearest_eq_rndDown_of_lt_midp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:02.57893+00:00
-- url     : https://prove2.me/theorems/7ab304cb-c196-4a64-bca8-d060c9b0758c
-- title:
--   Mpfx: nearest eq rnd Down of lt midp
-- statement:
--   **Below-midpoint ⟹ nearest rounds down.** If `ξ` lies strictly below its
--   `F`-midpoint, its round-to-nearest value (either tie-break) is `rndDown F ξ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L254-L269
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L254-L269

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.nearest_eq_rndDown_of_lt_midp (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : ξ < midp F ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndDown F ξ) := by sorry
