-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_neg_nearest
-- name    : Mpfx.RoundsFinite.neg_nearest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:48:27.953896+00:00
-- url     : https://prove2.me/theorems/a696f2cb-2d55-43c7-bae8-7a8c2c411eae
-- title:
--   Rounds Finite: neg nearest
-- statement:
--   Nearest rounding is invariant under joint negation (both tie-breaks).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L112-L116
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L112-L116

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.neg_nearest (F : FiniteFormat) (tb : TieBreak) (a : ℝ) (v : Dyadic) :
    RoundsFinite F (.nearest tb) a v ↔ RoundsFinite F (.nearest tb) (-a) (-v) := by sorry
