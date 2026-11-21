-- Prove2me | Theorems.Thm_Mpfx_Dyadic_ext_real
-- name    : Mpfx.Dyadic.ext_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:01.254819+00:00
-- url     : https://prove2.me/theorems/9a94f80d-3261-42aa-90e2-f426a37ff46a
-- title:
--   Dyadic: ext real
-- statement:
--   Extensionality through the real coercion: equal reals ⟹ equal dyadics.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L102-L104
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L102-L104

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

theorem Mpfx.Dyadic.ext_real {a b : Dyadic} (h : ((a : Dyadic) : ℝ) = ((b : Dyadic) : ℝ)) : a = b := by sorry
