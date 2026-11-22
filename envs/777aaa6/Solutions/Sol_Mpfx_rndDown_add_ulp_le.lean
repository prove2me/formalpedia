-- Prove2me | solution 1 for Mpfx.rndDown_add_ulp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:10:47.923625+00:00
-- url     : https://prove2.me/submissions/40410eab-f059-42ba-9576-e13027f9c3dc

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_ulp_of_ne_zero
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_int_mul_two_zpow_le_iff
import Theorems.Thm_Mpfx_mul_zpow_neg_self
import Theorems.Thm_Mpfx_two_zpow_split_toNat
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hle : F.canonicalExp x ≤ Int.log 2 x + 1) :
    (rndDown F x : ℝ) + ulp F x ≤ 2 ^ (Int.log 2 x + 1) := by
  rw [ulp_of_ne_zero F hx.ne', rndDown_eq, Dyadic.coe_ofIntZpow]
  set e := F.canonicalExp x
  set N : ℤ := 2 ^ (Int.log 2 x + 1 - e).toNat with hN_def
  have hN : (N : ℝ) * 2 ^ e = 2 ^ (Int.log 2 x + 1) := by
    rw [two_zpow_split_toNat (K := ℝ) hle, hN_def]; push_cast; ring
  have hlt : ⌊x * 2 ^ (-e)⌋ < N := by
    refine Int.floor_lt.mpr ((mul_lt_mul_iff_of_pos_right (zpow_pos two_pos e)).mp ?_)
    rw [mul_zpow_neg_self, hN]
    exact Int.lt_zpow_succ_log_self (by norm_num) x
  calc (⌊x * 2 ^ (-e)⌋ : ℝ) * 2 ^ e + 2 ^ e = ((⌊x * 2 ^ (-e)⌋ + 1 : ℤ) : ℝ) * 2 ^ e := by
        push_cast; ring
    _ ≤ (N : ℝ) * 2 ^ e := int_mul_two_zpow_le_iff.mpr (by omega)
    _ = _ := hN
end Mpfx
