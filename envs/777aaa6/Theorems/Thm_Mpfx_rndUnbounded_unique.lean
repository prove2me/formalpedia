-- Prove2me | Theorems.Thm_Mpfx_rndUnbounded_unique
-- name    : Mpfx.rndUnbounded_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:48.162184+00:00
-- url     : https://prove2.me/theorems/d0de3714-ff17-44d9-9458-62b9309bc118
-- title:
--   Mpfx: rnd Unbounded unique
-- statement:
--   Any `y` satisfying the spec equals `rndUnbounded F rm x h`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L34-L38
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L34-L38

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rndUnbounded_unique (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) {y : Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    y = rndUnbounded F rm x h := by sorry
