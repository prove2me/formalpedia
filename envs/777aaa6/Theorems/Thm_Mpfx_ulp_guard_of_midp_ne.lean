-- Prove2me | Theorems.Thm_Mpfx_ulp_guard_of_midp_ne
-- name    : Mpfx.ulp_guard_of_midp_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:46:36.375413+00:00
-- url     : https://prove2.me/theorems/c8485cda-c31b-4c37-ada4-5f8e21fc8c76
-- title:
--   Mpfx: ulp guard of midp ne
-- statement:
--   Without a minimum quantum `0` is its own midpoint, so any strict comparison
--   of `ξ` against `midp F ξ` rules the `ulp` guard out.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L110-L113
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L110-L113

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.ulp_guard_of_midp_ne {F : FiniteFormat} {ξ : ℝ} (h : ξ ≠ midp F ξ) :
    ¬(ξ = 0 ∧ F.exp = ⊥) := by sorry
