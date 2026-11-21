-- Prove2me | solution 1 for Mpfx.Dyadic.coe_rat_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:29:19.405508+00:00
-- url     : https://prove2.me/submissions/f90507df-638b-4537-852f-28fd818699b7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
attribute [local simp] Mpfx.Dyadic.coe_rat_half

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (y₁ y₂ : Dyadic) :
    ((midpoint y₁ y₂ : Dyadic) : ℚ) = (((y₁ : ℚ) + (y₂ : ℚ)) / 2) := by
  change (((y₁ + y₂) * half : Dyadic) : ℚ) = _
  push_cast [coe_rat_half]; ring
end Mpfx.Dyadic
