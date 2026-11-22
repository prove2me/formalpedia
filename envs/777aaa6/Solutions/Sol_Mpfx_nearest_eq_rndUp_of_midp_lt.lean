-- Prove2me | solution 1 for Mpfx.nearest_eq_rndUp_of_midp_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:33.466353+00:00
-- url     : https://prove2.me/submissions/3bf45899-5c4a-40f8-a960-77d1bd452750

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_ulp_eq_zpow_of
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_ulp_guard_of_midp_ne
import Theorems.Thm_Mpfx_nearest_eq_of_close
import Theorems.Thm_Mpfx_rndUp_eq
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_mul_zpow_neg_self
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : midp F ξ < ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndUp F ξ) := by
  set e := F.canonicalExp ξ with he
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hξ : ξ = (ξ * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := (mul_zpow_neg_self ξ e).symm
  have hmid : midp F ξ =
      (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e + (2 : ℝ) ^ e / 2 := by
    rw [midp, ulp_eq_zpow_of F (ulp_guard_of_midp_ne (ne_of_gt hlt)), rndDown_eq,
      Dyadic.coe_ofIntZpow, ← he]
  have hδ : (1 : ℝ) / 2 < ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
    rw [hmid] at hlt; nlinarith [hlt, h2e, hξ]
  have hceil : ⌈ξ * (2 : ℝ) ^ (-e)⌉ = ⌊ξ * (2 : ℝ) ^ (-e)⌋ + 1 :=
    le_antisymm (Int.ceil_le_floor_add_one _) (Int.lt_ceil.mpr (by linarith))
  have hclose : |ξ * (2 : ℝ) ^ (-e) - (⌈ξ * (2 : ℝ) ^ (-e)⌉ : ℝ)| < 1 / 2 := by
    rw [hceil]; push_cast; rw [abs_lt]
    exact ⟨by linarith [hδ], by linarith [Int.lt_floor_add_one (ξ * (2 : ℝ) ^ (-e))]⟩
  rw [rndUp_eq]
  exact nearest_eq_of_close F tb ξ hundef (he ▸ hclose)
end Mpfx
