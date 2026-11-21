-- Prove2me | Theorems.Thm_Mpfx_rnd_of_overflows
-- name    : Mpfx.rnd_of_overflows
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:56:45.750367+00:00
-- url     : https://prove2.me/theorems/b80bd9fb-90ee-4e3a-aea8-8c472e168aab
-- title:
--   Mpfx: rnd of overflows
-- statement:
--   An overflow selects the map's entry at the sign of `x`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L109-L115
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L109-L115

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rnd_of_overflows {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) (hov : Overflows F rm x) :
    rnd F S O rm (.finite x) = .value (O.map (decide (x < 0))) := by sorry
