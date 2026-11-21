-- Prove2me | Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
-- name    : Mpfx.coe_real_ofIntZpow_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:38.209846+00:00
-- url     : https://prove2.me/theorems/9a1a2df8-fa73-49b1-ae6b-ad847cb4a0ac
-- title:
--   Mpfx: coe real of Int Zpow one
-- statement:
--   `ofIntZpow 1 k` is `2^k` over `ℝ` (coefficient-free form).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L558-L560
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L558-L560

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
set_option autoImplicit true
open Mpfx

theorem Mpfx.coe_real_ofIntZpow_one (k : ℤ) :
    ((Dyadic.ofIntZpow 1 k : Dyadic) : ℝ) = (2 : ℝ) ^ k := by sorry
