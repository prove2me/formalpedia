-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_zpow_mem_unbounded
-- name    : Mpfx.FiniteFormat.zpow_mem_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:15.228204+00:00
-- url     : https://prove2.me/theorems/68882872-3d94-421e-aa1c-3ee551719049
-- title:
--   Finite Format: zpow mem unbounded
-- statement:
--   `2ʲ` is a value of `F` once `j` meets the minimum quantum.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L349-L351
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L349-L351

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.FiniteFormat.zpow_mem_unbounded (F : FiniteFormat) {j : ℤ}
    (hj : F.exp ≤ (j : QExp)) : Dyadic.ofIntZpow 1 j ∈ F.unbounded := by sorry
