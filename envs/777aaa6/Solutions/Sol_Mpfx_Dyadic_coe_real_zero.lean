-- Prove2me | solution 1 for Mpfx.Dyadic.coe_real_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:53.382403+00:00
-- url     : https://prove2.me/submissions/c4da4e6b-fc06-4507-b9da-363760f0994d

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
theorem _root_.solution :
    ((0 : Dyadic) : ℝ) = 0 := by push_cast; ring
end Mpfx.Dyadic
