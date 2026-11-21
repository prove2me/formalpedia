-- Prove2me | Theorems.Thm_Mpfx_rnd_mem_values
-- name    : Mpfx.rnd_mem_values
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:56:39.348187+00:00
-- url     : https://prove2.me/theorems/65ab63eb-96da-40b5-a187-757a98a9d7b1
-- title:
--   Mpfx: rnd mem values
-- statement:
--   Every value `rnd` returns is a value of `F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L120-L133
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L120-L133

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rnd_mem_values {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode} {v : WithSpecial ℝ}
    {w : WithSpecial Dyadic} (h : rnd F S O rm v = .value w) : w ∈ F.values := by sorry
