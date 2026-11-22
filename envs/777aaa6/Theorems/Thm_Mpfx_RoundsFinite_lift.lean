-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_lift
-- name    : Mpfx.RoundsFinite.lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:37.431079+00:00
-- url     : https://prove2.me/theorems/7a89d8c3-c278-4b08-a403-da74fd8a765d
-- title:
--   Rounds Finite: lift
-- statement:
--   **Lift**: if `w` is the bounded rounding of `x` and the unbounded rounding
--   `y` is in bound, then `w` is also the unbounded rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Restrict.lean#L237-L247
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Restrict.lean#L237-L247

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Restrict
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.lift {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F rm x w)
    (hy : RoundsFinite F.unbounded rm x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded rm x w := by sorry
