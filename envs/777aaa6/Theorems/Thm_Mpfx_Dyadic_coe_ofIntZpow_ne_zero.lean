-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow_ne_zero
-- name    : Mpfx.Dyadic.coe_ofIntZpow_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:17.224523+00:00
-- url     : https://prove2.me/theorems/8c9cdc5b-7076-43dc-8dcf-796e04ae4650
-- title:
--   Dyadic: coe of Int Zpow ne zero
-- statement:
--   `((ofIntZpow k e : Dyadic) : ℝ) ≠ 0` whenever `k ≠ 0`. Packages the
--   recurring `mul_ne_zero (cast) (zpow_pos)` idiom.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L455-L458
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L455-L458

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
open Mpfx.Dyadic

theorem Mpfx.Dyadic.coe_ofIntZpow_ne_zero {k : ℤ} (hk : k ≠ 0) (e : ℤ) :
    ((ofIntZpow k e : Dyadic) : ℝ) ≠ 0 := by sorry
