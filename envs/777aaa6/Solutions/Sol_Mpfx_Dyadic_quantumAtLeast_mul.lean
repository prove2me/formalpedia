-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:32:42.73487+00:00
-- url     : https://prove2.me/submissions/75a33e88-6f40-4455-9631-7852e0784dfc

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
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
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
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {e₁ e₂ : QExp} {x y : Dyadic}
    (hx : Dyadic.quantumAtLeast e₁ x) (hy : Dyadic.quantumAtLeast e₂ y) :
    Dyadic.quantumAtLeast (e₁ + e₂) (x * y) := by
  cases e₁ using QExp.recBotCoe with
  | bot => rw [show (⊥ + e₂ : QExp) = ⊥ from by simp]; trivial
  | coe a =>
    cases e₂ using QExp.recBotCoe with
    | bot => rw [show ((a : QExp) + ⊥) = ⊥ from by simp]; trivial
    | coe b =>
      obtain ⟨cx, hcx⟩ := (Dyadic.quantumAtLeast_coe_real a x).mp hx
      obtain ⟨cy, hcy⟩ := (Dyadic.quantumAtLeast_coe_real b y).mp hy
      rw [← WithBot.coe_add]
      refine (Dyadic.quantumAtLeast_coe_real (a + b) (x * y)).mpr ⟨cx * cy, ?_⟩
      rw [show ((x * y : Dyadic) : ℝ) = (x : ℝ) * (y : ℝ) from by push_cast; ring, hcx, hcy,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; push_cast; ring
end Mpfx.Dyadic
