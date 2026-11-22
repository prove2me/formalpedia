-- Prove2me | Theorems.Thm_Mpfx_rnd_of_mem_values
-- name    : Mpfx.rnd_of_mem_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:02.054513+00:00
-- url     : https://prove2.me/theorems/17e01531-57ff-4017-b083-711c11f169a2
-- title:
--   Mpfx: rnd of mem values
-- statement:
--   `rnd` fixes every value of `F` when `S` fixes the specials of `F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L136-L145
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L136-L145

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rnd_of_mem_values {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode}
    (hS : ∀ s ∈ F.specials, S.map s = .special s) (hrm : ¬ F.IsUndefined rm)
    {w : WithSpecial Dyadic} (hw : w ∈ F.values) : rnd F S O rm w.toReal = .value w := by sorry
