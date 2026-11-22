-- Prove2me | solution 1 for Mpfx.zpow_log_le_rndDown
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:07:40.213702+00:00
-- url     : https://prove2.me/submissions/3e42486e-f651-472b-82c6-3a7b926da731

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_max
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_IsAboveQuantum_le_log
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hq : F.IsAboveQuantum x) :
    (2 : ℝ) ^ (Int.log 2 x) ≤ ((rndDown F x : Dyadic) : ℝ) := by
  -- `2^⌊log₂ x⌋` is a value of `F` at most `x`.
  have hmem : Dyadic.ofIntZpow 1 (Int.log 2 x) ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun he' => (F.exp_le_canonicalExp x he').trans (hq.le_log hx))
      fun _ => by rw [abs_one]; exact one_le_pow₀ (by norm_num)
  have hle : ((Dyadic.ofIntZpow 1 (Int.log 2 x) : Dyadic) : ℝ) ≤ x := by
    rw [Dyadic.coe_ofIntZpow, Int.cast_one, one_mul]; exact Int.zpow_log_le_self (by norm_num) hx
  have h := rndDown_max F x hmem hle
  rwa [Dyadic.coe_ofIntZpow, Int.cast_one, one_mul] at h
end Mpfx
