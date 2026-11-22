-- Prove2me | solution 1 for Mpfx.isAboveQuantum_of_rndDown_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:06:25.028185+00:00
-- url     : https://prove2.me/submissions/3f8a9f71-de2c-457c-8e7e-b76ea9e38a8e

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_rndDown_le
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_isAboveQuantum_of_le_log
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {x : ℝ}
    (h : 0 < ((rndDown F x : Dyadic) : ℝ)) : F.IsAboveQuantum x := by
  have hx : 0 < x := lt_of_lt_of_le h (rndDown_le F x)
  refine FiniteFormat.isAboveQuantum_of_le_log hx ?_
  set e := F.canonicalExp x with he
  by_contra hc
  push Not at hc
  have hxe : x * (2 : ℝ) ^ (-e) < 1 := by
    have hkhi : x < (2 : ℝ) ^ (Int.log 2 x + 1) := Int.lt_zpow_succ_log_self (by norm_num) x
    have h1 : x < (2 : ℝ) ^ e :=
      lt_of_lt_of_le hkhi (zpow_le_zpow_right₀ (by norm_num) (by omega))
    calc x * (2 : ℝ) ^ (-e) < (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) := by
          nlinarith [zpow_pos (show (0 : ℝ) < 2 by norm_num) (-e)]
      _ = 1 := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  have hfl : ⌊x * (2 : ℝ) ^ (-e)⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by positivity, hxe⟩
  rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he, hfl] at h
  norm_num at h
end Mpfx
