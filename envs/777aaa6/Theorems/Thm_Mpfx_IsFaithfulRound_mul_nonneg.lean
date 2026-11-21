-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_mul_nonneg
-- name    : Mpfx.IsFaithfulRound.mul_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:44:03.237212+00:00
-- url     : https://prove2.me/theorems/0bd015a9-ec2c-4ee6-86d9-0fbd86cb99df
-- title:
--   Is Faithful Round: mul nonneg
-- statement:
--   A faithful rounding has the sign of its input.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L681-L686
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L681-L686

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.mul_nonneg {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) : (z : ℝ) * x ≥ 0 := by sorry
