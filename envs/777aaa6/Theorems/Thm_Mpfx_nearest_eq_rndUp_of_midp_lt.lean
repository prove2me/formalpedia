-- Prove2me | Theorems.Thm_Mpfx_nearest_eq_rndUp_of_midp_lt
-- name    : Mpfx.nearest_eq_rndUp_of_midp_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:00.349254+00:00
-- url     : https://prove2.me/theorems/b3252c60-f2a2-4eb8-9dcd-6c0c85575ae8
-- title:
--   Mpfx: nearest eq rnd Up of midp lt
-- statement:
--   **Above-midpoint ⟹ nearest rounds up**, mirroring
--   `nearest_eq_rndDown_of_lt_midp`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L278-L296
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L278-L296

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.nearest_eq_rndUp_of_midp_lt (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : midp F ξ < ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndUp F ξ) := by sorry
