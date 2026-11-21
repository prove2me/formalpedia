-- Prove2me | solution 1 for Mpfx.Format.b_top_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:48.083834+00:00
-- url     : https://prove2.me/submissions/af0779ca-bf47-4a4b-b57e-6fd8f0dcd019

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_exists_zpow_gt
import Theorems.Thm_Mpfx_Format_ofIntZpow_mem
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_precisionAtMost_one_zpow


set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F₁ F₂ : Format} (hp : F₁.p ≠ 0) (hb : F₁.b = ⊤) (h : F₁ ⊆ F₂) :
    F₂.b = ⊤ := by
  by_contra hne
  obtain ⟨b₂, hb₂⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨k, hk, hgt⟩ := exists_zpow_gt ((b₂.val : Dyadic) : ℝ) F₁.exp
  have hv := (h _ (ofIntZpow_mem (precisionAtMost_one_zpow hp k) hk (by rw [hb]; trivial))).2.2
  rw [← hb₂] at hv
  have := abs_coe_real_le_of_boundOK hv
  rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos (by norm_num) k)] at this
  exact absurd this (not_le_of_gt hgt)
end Mpfx.Format
