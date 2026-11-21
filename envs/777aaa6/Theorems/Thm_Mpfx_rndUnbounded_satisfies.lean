-- Prove2me | Theorems.Thm_Mpfx_rndUnbounded_satisfies
-- name    : Mpfx.rndUnbounded_satisfies
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:20.294889+00:00
-- url     : https://prove2.me/theorems/d755eb7a-2756-40e6-92d3-2d3c34525b97
-- title:
--   Mpfx: rnd Unbounded satisfies
-- statement:
--   `rndUnbounded` satisfies the unbounded rounding spec.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L21-L30
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L21-L30

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rndUnbounded_satisfies (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) :
    RoundsFinite F.unbounded rm x (rndUnbounded F rm x h) := by sorry
