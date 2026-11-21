-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_nonneg
-- name    : Mpfx.IsFaithfulRound.nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:43:59.628861+00:00
-- url     : https://prove2.me/theorems/56aa9093-a552-4d54-b531-e7f4429fc695
-- title:
--   Is Faithful Round: nonneg
-- statement:
--   A faithful rounding of a nonnegative input is nonnegative.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L667-L671
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L667-L671

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.nonneg {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) (hx : 0 ≤ x) : 0 ≤ (z : ℝ) := by sorry
