-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
-- name    : Mpfx.RoundsFinite.isFaithfulRound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:15.309488+00:00
-- url     : https://prove2.me/theorems/fa221be5-bb50-4550-941c-ecfd53af2a1d
-- title:
--   Rounds Finite: is Faithful Round
-- statement:
--   Whatever the mode, the rounded value is the round-down or the round-up of
--   `x`. `isFaithfulRound_iff_directed` reads the result back as the two-sided
--   disjunction (Flocq `Zrnd_DN_or_UP`, `Rnd_N_pt_DN_or_UP`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L267-L286
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L267-L286

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.isFaithfulRound {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F rm x y) :
    IsFaithfulRound F x y := by sorry
