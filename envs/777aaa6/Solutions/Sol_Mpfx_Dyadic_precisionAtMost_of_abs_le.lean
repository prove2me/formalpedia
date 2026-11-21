-- Prove2me | solution 1 for Mpfx.Dyadic.precisionAtMost_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:32:43.626981+00:00
-- url     : https://prove2.me/submissions/154cc8a4-b14f-4928-ab67-ebdecbc9a4dd

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
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe
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
theorem _root_.solution {p : ℕ} (hp : 0 < p) {x : Dyadic} (c e : ℤ)
    (hx : (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e) (hc : |c| ≤ (2 : ℤ) ^ p) :
    precisionAtMost (p : Prec) x := by
  rw [precisionAtMost_coe]
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact ⟨c, e, hx, hlt⟩
  · have h2p_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ p := by positivity
    have hsign : c = (2 : ℤ) ^ p ∨ c = -((2 : ℤ) ^ p) :=
      (abs_eq h2p_nonneg).mp heq
    have hone_lt : (1 : ℤ) < (2 : ℤ) ^ p := by
      have : (2 : ℤ) ^ 0 < (2 : ℤ) ^ p := pow_lt_pow_right₀ (by norm_num) hp
      simpa using this
    -- `c = ±2^p` renormalises to `±1 · 2^(e+p)`.
    obtain ⟨s, hs, hcs⟩ : ∃ s : ℤ, |s| = 1 ∧ c = s * 2 ^ p := by
      rcases hsign with h | h
      exacts [⟨1, by simp, by simp [h]⟩, ⟨-1, by simp, by simp [h]⟩]
    refine ⟨s, e + (p : ℤ), ?_, by rw [hs]; exact hone_lt⟩
    rw [hx, hcs, zpow_add₀ two_ne_zero]
    push_cast
    simp only [← zpow_natCast (2 : ℚ) p]
    ring
end Mpfx.Dyadic
