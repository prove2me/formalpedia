-- Prove2me | Theorems.Thm_Mpfx_rndUnbounded_satisfies_toOdd
-- name    : Mpfx.rndUnbounded_satisfies_toOdd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:56:28.890535+00:00
-- url     : https://prove2.me/theorems/da4aa30f-8f7b-461c-a571-afa7284e1985
-- title:
--   Mpfx: rnd Unbounded satisfies to Odd
-- statement:
--   The Mpfx construction uses the rnd Unbounded satisfies to Odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/ToOdd.lean#L17-L34
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/ToOdd.lean#L17-L34

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rndUnbounded_satisfies_toOdd (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) :
    RoundsFinite F.unbounded .toOdd x (rndUnbounded F .toOdd x h) := by sorry
