-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_neg_iff
-- name    : Mpfx.IsFaithfulRound.neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:08:47.398657+00:00
-- url     : https://prove2.me/theorems/3bd93782-64d7-4127-98e1-f480a403c61f
-- title:
--   Is Faithful Round: neg iff
-- statement:
--   `IsFaithfulRound` is invariant under joint negation of `x` and `y`. The
--   two disjuncts swap roles: a max-below witness for `x` becomes a min-above
--   witness for `-x`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L32-L39
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L32-L39

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff


set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.neg_iff (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    IsFaithfulRound F x y ↔ IsFaithfulRound F (-x) (-y) := by sorry
