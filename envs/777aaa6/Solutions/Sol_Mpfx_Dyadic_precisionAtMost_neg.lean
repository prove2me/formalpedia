-- Prove2me | solution 1 for Mpfx.Dyadic.precisionAtMost_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:29:29.050167+00:00
-- url     : https://prove2.me/submissions/7562f5b7-4e00-4046-8e8b-fc1e0b8bb6e2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local norm_cast] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local norm_cast] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local norm_cast] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local norm_cast] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local norm_cast] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local norm_cast] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {p : Prec} {x : Dyadic} (h : precisionAtMost p x) :
    precisionAtMost p (-x) := by
  cases p using ENat.recTopCoe with
  | top => trivial
  | coe p =>
    obtain ⟨c, e, hx, hc⟩ := h
    refine ⟨-c, e, ?_, ?_⟩
    · push_cast [Subring.coe_neg, hx]; ring
    · simpa [abs_neg] using hc
end Mpfx.Dyadic
