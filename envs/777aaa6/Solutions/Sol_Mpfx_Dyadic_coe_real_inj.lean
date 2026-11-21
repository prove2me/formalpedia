-- Prove2me | solution 1 for Mpfx.Dyadic.coe_real_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:30.348175+00:00
-- url     : https://prove2.me/submissions/f8aeb9ad-b6ec-45a7-9b57-21e8d9365c5c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_ext_real

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (a b : Dyadic) :
    ((a : Dyadic) : ℝ) = ((b : Dyadic) : ℝ) ↔ a = b :=
  ⟨ext_real, fun h => by rw [h]⟩
end Mpfx.Dyadic
