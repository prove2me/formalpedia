-- Prove2me | solution 1 for Mpfx.Dyadic.isRepresentableAtP_of_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:32:44.076017+00:00
-- url     : https://prove2.me/submissions/1a90677d-0316-4fdf-9848-2105dc06b4bb

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
theorem _root_.solution {k e' : ℤ} (hk : k ≠ 0) {y : Dyadic}
    (hy : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e') :
    IsRepresentableAtP ((Int.log 2 (|k| : ℝ)).toNat + 1) k e' y := by
  have h_one_le : (1 : ℝ) ≤ (|k| : ℝ) := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
    exact_mod_cast h1
  have h_abs_pos : (0 : ℝ) < (|k| : ℝ) := by linarith
  have h_log_nn : 0 ≤ Int.log 2 (|k| : ℝ) := by
    rw [show (0 : ℤ) = Int.log 2 (1 : ℝ) by simp [Int.log_one_right]]
    exact Int.log_mono_right (by norm_num) h_one_le
  refine ⟨hy, ?_, ?_⟩
  · have h_simp : (Int.log 2 (|k| : ℝ)).toNat + 1 - 1 = (Int.log 2 (|k| : ℝ)).toNat := by
      omega
    rw [h_simp]
    have h_2pow_le : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) ≤ (|k| : ℝ) :=
      Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) h_abs_pos
    have h_nat : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_nn
    have h_cast : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) =
        (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) := by
      rw [show (Int.log 2 (|k| : ℝ)) = ((Int.log 2 (|k| : ℝ)).toNat : ℤ) from
        h_nat.symm, zpow_natCast]
      push_cast; rfl
    have h_real_le : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) ≤ (|k| : ℝ) := by
      rw [h_cast]; exact h_2pow_le
    exact_mod_cast h_real_le
  · have h_2pow_gt : (|k| : ℝ) < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) :=
      Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
    have h_cast : ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) =
        (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) := by
      push_cast
      rw [← zpow_natCast (2 : ℝ) ((Int.log 2 (|k| : ℝ)).toNat + 1)]
      congr 1; push_cast; omega
    have h_real_lt : (|k| : ℝ) <
        ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) := by
      rw [h_cast]; exact h_2pow_gt
    exact_mod_cast h_real_lt
end Mpfx.Dyadic
