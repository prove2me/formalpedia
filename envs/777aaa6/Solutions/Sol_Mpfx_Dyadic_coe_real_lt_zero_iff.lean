-- Prove2me | solution 1 for Mpfx.Dyadic.coe_real_lt_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:20.647687+00:00
-- url     : https://prove2.me/submissions/bfe301ed-99f1-423f-9b45-76c0baf3bf63

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (d : Dyadic) : (d : ℝ) < 0 ↔ (d : ℚ) < 0 := by
  rw [coe_real_eq_ratCast, Rat.cast_lt_zero]
end Mpfx.Dyadic
