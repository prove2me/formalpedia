-- Prove2me | solution 1 for Mpfx.coe_real_ofIntZpow_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:41.008437+00:00
-- url     : https://prove2.me/submissions/61e6eb7c-4026-4a58-9b99-e86be94e7c08

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (k : ℤ) :
    ((Dyadic.ofIntZpow 1 k : Dyadic) : ℝ) = (2 : ℝ) ^ k := by
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring
end Mpfx
