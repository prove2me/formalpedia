-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
-- name    : Mpfx.Dyadic.coe_rat_ofIntZpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:19:47.317584+00:00
-- url     : https://prove2.me/theorems/e25c9ba3-9302-4f13-94cd-cc3fc894cedb
-- title:
--   Dyadic: coe rat of Int Zpow
-- statement:
--   The Dyadic construction uses the coe rat of Int Zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L164-L165
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L164-L165

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

theorem Mpfx.Dyadic.coe_rat_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := by sorry

attribute [defeq] Mpfx.Dyadic.coe_rat_ofIntZpow
