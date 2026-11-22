-- Prove2me | solution 1 for Mpfx.lt_rndDown_add_ulp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:47.093119+00:00
-- url     : https://prove2.me/submissions/f8c96151-4b0f-434c-a27d-307ac425fd80

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_ulp_eq_zpow_of
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_mul_zpow_neg_self
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {x : ℝ}
    (hx : ¬(x = 0 ∧ F.exp = ⊥)) :
    x < (rndDown F x : ℝ) + ulp F x := by
  rw [rndDown_eq, Dyadic.coe_ofIntZpow]
  set e := F.canonicalExp x with he
  set t := x * (2 : ℝ) ^ (-e) with ht
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hxt : x = t * (2 : ℝ) ^ e := by rw [ht, mul_zpow_neg_self]
  have hfloor : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlt : t * (2 : ℝ) ^ e < ((⌊t⌋ : ℝ) + 1) * (2 : ℝ) ^ e :=
    mul_lt_mul_of_pos_right hfloor h2
  rw [← hxt] at hlt
  have hulp : ulp F x = (2 : ℝ) ^ e := by rw [ulp_eq_zpow_of F hx, ← he]
  rw [hulp]
  nlinarith [hlt]
end Mpfx
