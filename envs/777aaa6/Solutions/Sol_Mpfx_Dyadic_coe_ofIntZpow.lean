-- Prove2me | solution 1 for Mpfx.Dyadic.coe_ofIntZpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:52.285816+00:00
-- url     : https://prove2.me/submissions/5a3444af-775a-4266-98cb-d64c562fd3fc

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
theorem _root_.solution (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  change ((((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ)) = (c : ℝ) * (2 : ℝ) ^ e
  push_cast; ring
end Mpfx.Dyadic
