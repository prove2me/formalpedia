-- Prove2me | solution 1 for Mpfx.Dyadic.coe_ofIntZpow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:28:43.864448+00:00
-- url     : https://prove2.me/submissions/0b931db1-4c72-4e0a-ac28-3061f8c4fdba

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {k : ℤ} (hk : k ≠ 0) (e : ℤ) :
    ((ofIntZpow k e : Dyadic) : ℝ) ≠ 0 := by
  rw [coe_ofIntZpow]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hk) (ne_of_gt (zpow_pos (by norm_num) _))
end Mpfx.Dyadic
