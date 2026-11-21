-- Prove2me | solution 1 for Mpfx.Dyadic.coe_real_eq_ratCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:59.465643+00:00
-- url     : https://prove2.me/submissions/8aab7a83-6264-4ea8-8eda-dc313c291805

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
    ((d : Dyadic) : ℝ) = ((d : ℚ) : ℝ) := rfl
end Mpfx.Dyadic
