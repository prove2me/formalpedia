-- Prove2me | Theorems.Thm_Mpfx_rndUnbounded_satisfies_nearest
-- name    : Mpfx.rndUnbounded_satisfies_nearest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:27.417179+00:00
-- url     : https://prove2.me/theorems/6c16ff03-ba2a-4114-8e94-1f342d384dab
-- title:
--   Mpfx: rnd Unbounded satisfies nearest
-- statement:
--   The Mpfx construction uses the rnd Unbounded satisfies nearest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Nearest.lean#L21-L90
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Nearest.lean#L21-L90

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Nearest
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rndUnbounded_satisfies_nearest (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) :
    RoundsFinite F.unbounded (.nearest tb) x (rndUnbounded F (.nearest tb) x h) := by sorry
