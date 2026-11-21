-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
-- name    : Mpfx.Dyadic.coe_ofIntZpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:19:44.888179+00:00
-- url     : https://prove2.me/theorems/add16474-b5c0-4b9b-a932-eedd80542c7b
-- title:
--   Dyadic: coe of Int Zpow
-- statement:
--   The Dyadic construction uses the coe of Int Zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L167-L170
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L167-L170

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

theorem Mpfx.Dyadic.coe_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by sorry
