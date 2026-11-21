-- Prove2me | solution 1 for Mpfx.Dyadic.coe_rat_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:21:02.842869+00:00
-- url     : https://prove2.me/submissions/e9cb2b92-a224-448b-96f9-7bbb59dbeb86

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution : ((half : Dyadic) : ℚ) = 1 / 2 := by
  change ((ofIntZpow 1 (-1) : Dyadic) : ℚ) = 1 / 2
  rw [coe_rat_ofIntZpow, zpow_neg_one]; push_cast; ring
end Mpfx.Dyadic
