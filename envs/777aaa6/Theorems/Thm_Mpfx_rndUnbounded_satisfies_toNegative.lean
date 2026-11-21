-- Prove2me | Theorems.Thm_Mpfx_rndUnbounded_satisfies_toNegative
-- name    : Mpfx.rndUnbounded_satisfies_toNegative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:56:24.85472+00:00
-- url     : https://prove2.me/theorems/0d9ac34e-885b-4b7e-b504-cc237dc18fda
-- title:
--   Mpfx: rnd Unbounded satisfies to Negative
-- statement:
--   The Mpfx construction uses the rnd Unbounded satisfies to Negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Directed.lean#L17-L20
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Directed.lean#L17-L20

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Directed
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rndUnbounded_satisfies_toNegative (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) :
    RoundsFinite F.unbounded .toNegative x (rndUnbounded F .toNegative x h) := by sorry
