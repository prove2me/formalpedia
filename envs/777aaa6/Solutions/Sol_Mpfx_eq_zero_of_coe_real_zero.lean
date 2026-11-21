-- Prove2me | solution 1 for Mpfx.eq_zero_of_coe_real_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:26:30.230313+00:00
-- url     : https://prove2.me/submissions/54ddc28c-21a7-4223-8853-45884356c445

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local norm_cast] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local norm_cast] Mpfx.Dyadic.coe_real_zero

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {z : Dyadic} (h : (z : ℝ) = 0) : z = 0 :=
  (Dyadic.coe_real_inj z 0).mp (by rw [h, Dyadic.coe_real_zero])
end Mpfx
