-- Prove2me | solution 1 for Mpfx.Dyadic.coe_rat_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:20:45.696672+00:00
-- url     : https://prove2.me/submissions/b987f2c6-71e2-4557-bf58-718bbe130f5a

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
namespace Mpfx.Dyadic
theorem _root_.solution (x : Dyadic) : ((Dyadic.abs x : Dyadic) : ℚ) = |(x : ℚ)| := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℚ)
  · rw [if_pos h, _root_.abs_of_nonneg h]
  · rw [if_neg h, Subring.coe_neg, _root_.abs_of_neg (lt_of_not_ge h)]
end Mpfx.Dyadic
