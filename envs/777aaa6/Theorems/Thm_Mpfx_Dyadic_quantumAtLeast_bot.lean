-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
-- name    : Mpfx.Dyadic.quantumAtLeast_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:20:40.676886+00:00
-- url     : https://prove2.me/theorems/a36b6d6b-5433-490d-a90a-d7126b36f087
-- title:
--   Dyadic: quantum At Least bot
-- statement:
--   The Dyadic construction uses the quantum At Least bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L215-L215
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L215-L215

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

theorem Mpfx.Dyadic.quantumAtLeast_bot (x : Dyadic) : quantumAtLeast ⊥ x := by sorry
