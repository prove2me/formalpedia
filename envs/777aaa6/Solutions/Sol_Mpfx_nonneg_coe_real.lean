-- Prove2me | solution 1 for Mpfx.nonneg_coe_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:34.547176+00:00
-- url     : https://prove2.me/submissions/6d0d6016-c043-4249-ac6e-18b2202018fc

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
namespace Mpfx
theorem _root_.solution (b : NonNegDyadic) : 0 ≤ ((b.val : Dyadic) : ℝ) := by
  exact_mod_cast b.2
end Mpfx
