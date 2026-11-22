-- Prove2me | Theorems.Thm_Mpfx_rnd_iff_rounds
-- name    : Mpfx.rnd_iff_rounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:59.537186+00:00
-- url     : https://prove2.me/theorems/b13283d9-96fe-4347-a952-e8d7e357e9e2
-- title:
--   Mpfx: rnd iff rounds
-- statement:
--   The Mpfx construction uses the rnd iff rounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L52-L90
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L52-L90

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rnd_iff_rounds (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (rm : RoundingMode) (v : WithSpecial ℝ) (r : RoundResult) :
    rnd F S O rm v = r ↔ Rounds F S O rm v r := by sorry
