-- Prove2me | solution 1 for Mpfx.Dyadic.coe_real_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:20:19.28358+00:00
-- url     : https://prove2.me/submissions/20cbd4a8-22ca-4d7e-9526-47e752630a91

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
theorem _root_.solution (d₁ d₂ : Dyadic) :
    ((d₁ * d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) * ((d₂ : Dyadic) : ℝ) := by
  push_cast; ring
end Mpfx.Dyadic
