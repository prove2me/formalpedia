-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
-- name    : Mpfx.IsFaithfulRound.eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:50.594296+00:00
-- url     : https://prove2.me/theorems/eeda5eaa-1af3-4695-976e-7e00d81209f4
-- title:
--   Is Faithful Round: eq of mem
-- statement:
--   A faithful rounding of a representable value is that value.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L51-L55
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L51-L55

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.eq_of_mem {F : FiniteFormat} {d y : Dyadic} (hd : d ∈ F)
    (h : IsFaithfulRound F (d : ℝ) y) : y = d := by sorry
