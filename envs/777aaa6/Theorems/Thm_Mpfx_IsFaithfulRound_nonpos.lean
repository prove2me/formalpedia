-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_nonpos
-- name    : Mpfx.IsFaithfulRound.nonpos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:43:53.592731+00:00
-- url     : https://prove2.me/theorems/e9c4da3d-18fb-4170-b064-5b8ca6106a11
-- title:
--   Is Faithful Round: nonpos
-- statement:
--   A faithful rounding of a nonpositive input is nonpositive.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L674-L678
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L674-L678

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.nonpos {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) (hx : x ≤ 0) : (z : ℝ) ≤ 0 := by sorry
