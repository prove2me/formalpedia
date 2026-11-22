-- Prove2me | Theorems.Thm_Mpfx_overflows_iff_not_roundsInBound
-- name    : Mpfx.overflows_iff_not_roundsInBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:56:34.724185+00:00
-- url     : https://prove2.me/theorems/c1c90d4c-3d68-4efd-8ac3-7979c3fb2127
-- title:
--   Mpfx: overflows iff not rounds In Bound
-- statement:
--   For a defined mode, a real either overflows or rounds within the bound.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L41-L48
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L41-L48

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.overflows_iff_not_roundsInBound {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) : Overflows F rm x ↔ ¬ ∃ y, RoundsInBound F rm x y := by sorry
