-- Prove2me | solution 1 for Mpfx.Dyadic.coe_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:04.158456+00:00
-- url     : https://prove2.me/submissions/7ed4e18d-3205-4691-9acb-e5456b76f7ff

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_half
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local norm_cast] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local norm_cast] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_half

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (y₁ y₂ : Dyadic) :
    ((midpoint y₁ y₂ : Dyadic) : ℝ) = ((y₁ : ℝ) + (y₂ : ℝ)) / 2 := by
  change (((y₁ + y₂) * half : Dyadic) : ℝ) = _
  rw [coe_real_mul, coe_real_add, coe_half]; ring
end Mpfx.Dyadic
