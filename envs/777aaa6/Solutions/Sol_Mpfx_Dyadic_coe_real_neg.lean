-- Prove2me | solution 1 for Mpfx.Dyadic.coe_real_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:52.807226+00:00
-- url     : https://prove2.me/submissions/b1e3ad86-282c-4987-8356-a8152a0c1c23

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
theorem _root_.solution (d : Dyadic) :
    ((-d : Dyadic) : ℝ) = -((d : Dyadic) : ℝ) := by
  push_cast; ring
end Mpfx.Dyadic
