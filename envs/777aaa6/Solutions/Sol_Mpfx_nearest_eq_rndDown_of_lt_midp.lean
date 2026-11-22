-- Prove2me | solution 1 for Mpfx.nearest_eq_rndDown_of_lt_midp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:30.41036+00:00
-- url     : https://prove2.me/submissions/f10a7e12-b218-4b41-b4b0-d25b874bc1b0

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_ulp_eq_zpow_of
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_ulp_guard_of_midp_ne
import Theorems.Thm_Mpfx_nearest_eq_of_close
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_mul_zpow_neg_self
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : ξ < midp F ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndDown F ξ) := by
  set e := F.canonicalExp ξ with he
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hξ : ξ = (ξ * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := (mul_zpow_neg_self ξ e).symm
  have hmid : midp F ξ =
      (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e + (2 : ℝ) ^ e / 2 := by
    rw [midp, ulp_eq_zpow_of F (ulp_guard_of_midp_ne (ne_of_lt hlt)), rndDown_eq,
      Dyadic.coe_ofIntZpow, ← he]
  have hδ : ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < 1 / 2 := by
    rw [hmid] at hlt; nlinarith [hlt, h2e, hξ]
  have hclose : |ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ)| < 1 / 2 := by
    rw [abs_lt]; exact ⟨by linarith [Int.floor_le (ξ * (2 : ℝ) ^ (-e))], hδ⟩
  rw [rndDown_eq]
  exact nearest_eq_of_close F tb ξ hundef (he ▸ hclose)
end Mpfx
