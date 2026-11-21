-- Prove2me | Theorems.Thm_Mpfx_rnd_special
-- name    : Mpfx.rnd_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:44:57.82734+00:00
-- url     : https://prove2.me/theorems/b1dceb5e-b4e9-46cd-b319-96511ebbe86e
-- title:
--   Mpfx: rnd special
-- statement:
--   The Mpfx construction uses the rnd special property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L104-L106
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L104-L106

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rnd_special (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (rm : RoundingMode) (s : Special) :
    rnd F S O rm (.special s) = .value (S.map s) := by sorry

attribute [defeq] Mpfx.rnd_special
