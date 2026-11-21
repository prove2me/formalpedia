-- Prove2me | solution 1 for Mpfx.Dyadic.midpoint_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:12.499666+00:00
-- url     : https://prove2.me/submissions/be0d21b6-f770-4d75-be22-8ea6b4bc35ff

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_coe_midpoint

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (y₁ y₂ : Dyadic) :
    midpoint y₁ y₂ = midpoint y₂ y₁ := by
  apply ext_real
  rw [coe_midpoint, coe_midpoint]; ring
end Mpfx.Dyadic
