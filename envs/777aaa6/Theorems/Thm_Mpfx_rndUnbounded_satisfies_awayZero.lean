-- Prove2me | Theorems.Thm_Mpfx_rndUnbounded_satisfies_awayZero
-- name    : Mpfx.rndUnbounded_satisfies_awayZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:56:22.979328+00:00
-- url     : https://prove2.me/theorems/5870c0dd-eed6-43e5-a682-910ef66d2f2b
-- title:
--   Mpfx: rnd Unbounded satisfies away Zero
-- statement:
--   The Mpfx construction uses the rnd Unbounded satisfies away Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Directed.lean#L39-L49
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Directed.lean#L39-L49

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Directed
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rndUnbounded_satisfies_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by sorry
