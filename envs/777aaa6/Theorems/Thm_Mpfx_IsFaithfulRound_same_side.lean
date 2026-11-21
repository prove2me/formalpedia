-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_same_side
-- name    : Mpfx.IsFaithfulRound.same_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:56:07.286097+00:00
-- url     : https://prove2.me/theorems/34d2d20c-049a-4c39-931c-2c1760466f2c
-- title:
--   Is Faithful Round: same side
-- statement:
--   A faithful rounding stays on its input's side of any value `m` of the format
--   that neither equals.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L392-L399
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L392-L399

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.same_side {F : FiniteFormat} {x : ℝ} {z m : Dyadic}
    (h : IsFaithfulRound F x z) (hm : m ∈ F) (hxm : x ≠ (m : ℝ)) (hzm : (z : ℝ) ≠ m) :
    0 < (x - m) * ((z : ℝ) - m) := by sorry
