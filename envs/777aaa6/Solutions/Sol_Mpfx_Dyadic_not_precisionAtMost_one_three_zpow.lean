-- Prove2me | solution 1 for Mpfx.Dyadic.not_precisionAtMost_one_three_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:34:16.193803+00:00
-- url     : https://prove2.me/submissions/c05d5eb3-dfb3-4265-80cb-9e7117743f7e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_not_precisionAtMost_of_odd
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (k : ℤ) :
    ¬ precisionAtMost ((1 : ℕ) : Prec) (Dyadic.ofIntZpow 3 k) :=
  not_precisionAtMost_of_odd (by norm_num : Odd (3 : ℤ)) (by rw [coe_ofIntZpow]) (by norm_num)
end Mpfx.Dyadic
