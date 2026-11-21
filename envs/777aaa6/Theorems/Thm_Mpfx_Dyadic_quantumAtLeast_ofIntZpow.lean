-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_ofIntZpow
-- name    : Mpfx.Dyadic.quantumAtLeast_ofIntZpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:32.430259+00:00
-- url     : https://prove2.me/theorems/b4d3b14a-181c-47f5-9d32-9758ca92b0b2
-- title:
--   Dyadic: quantum At Least of Int Zpow
-- statement:
--   `c · 2^k` has quantum at least `2^e` for every `e ≤ k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L285-L287
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L285-L287

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

theorem Mpfx.Dyadic.quantumAtLeast_ofIntZpow {e : QExp} {c k : ℤ} (he : e ≤ (k : QExp)) :
    quantumAtLeast e (ofIntZpow c k) := by sorry
