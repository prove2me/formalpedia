-- Prove2me | solution 1 for Mpfx.Dyadic.coe_real_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:59.261176+00:00
-- url     : https://prove2.me/submissions/7fe68eb7-422e-406a-b7bb-9c4fa0488a10

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
    ((d₁ + d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) + ((d₂ : Dyadic) : ℝ) := by
  push_cast; ring
end Mpfx.Dyadic
