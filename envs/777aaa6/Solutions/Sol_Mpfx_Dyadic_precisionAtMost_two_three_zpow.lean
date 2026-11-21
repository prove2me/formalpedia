-- Prove2me | solution 1 for Mpfx.Dyadic.precisionAtMost_two_three_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:19.251119+00:00
-- url     : https://prove2.me/submissions/64e8e144-81f5-4e73-bc8c-12a1084298a0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (k : ℤ) :
    precisionAtMost ((2 : ℕ) : Prec) (Dyadic.ofIntZpow 3 k) := by
  rw [precisionAtMost_coe]
  refine ⟨3, k, ?_, ?_⟩
  · rw [coe_rat_ofIntZpow]
  · decide
end Mpfx.Dyadic
