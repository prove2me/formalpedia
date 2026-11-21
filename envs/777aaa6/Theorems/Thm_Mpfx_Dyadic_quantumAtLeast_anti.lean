-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti
-- name    : Mpfx.Dyadic.quantumAtLeast_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:48.043248+00:00
-- url     : https://prove2.me/theorems/aeff0ed0-bce0-4c2e-a4d4-603aa94e2aba
-- title:
--   Dyadic: quantum At Least anti
-- statement:
--   `quantumAtLeast` is antitone in the exponent bound: a smaller minimum
--   quantum (smaller `exp`) is a weaker constraint.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L273-L282
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L273-L282

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

theorem Mpfx.Dyadic.quantumAtLeast_anti {e₁ e₂ : QExp} (h : e₂ ≤ e₁) {x : Dyadic}
    (hx : quantumAtLeast e₁ x) : quantumAtLeast e₂ x := by sorry
