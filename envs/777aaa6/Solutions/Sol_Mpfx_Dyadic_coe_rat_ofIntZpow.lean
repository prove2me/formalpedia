-- Prove2me | solution 1 for Mpfx.Dyadic.coe_rat_ofIntZpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:54.024761+00:00
-- url     : https://prove2.me/submissions/6a5b67f6-5e64-4c0b-83c0-0561267ac6aa

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
    ((ofIntZpow c e : Dyadic) : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := rfl
end Mpfx.Dyadic
