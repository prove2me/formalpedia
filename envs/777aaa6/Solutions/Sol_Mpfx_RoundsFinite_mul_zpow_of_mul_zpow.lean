-- Prove2me | solution 1 for Mpfx.RoundsFinite.mul_zpow_of_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:26:03.243485+00:00
-- url     : https://prove2.me/submissions/6461d8c0-84ea-4526-81bc-29d5b0c959f7

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_RoundsFinite_exists_mul_zpow
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_mem_unbounded_of_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem
import Theorems.Thm_Mpfx_two_zpow_shift
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded rm x y) {z k : ℤ} (hx : x = z * (2 : ℝ) ^ k) :
    ∃ c : ℤ, (y : ℝ) = c * (2 : ℝ) ^ k := by
  obtain ⟨c, hc⟩ := h.exists_mul_zpow
  rcases le_total k (F.canonicalExp x) with hk | hk
  · exact ⟨_, hc.trans (two_zpow_shift c hk)⟩
  · -- `x` is a multiple of `2^canonicalExp x`, so a value of `F` that rounds to itself.
    have hd : ((Dyadic.ofIntZpow z k : Dyadic) : ℝ) = x := by rw [Dyadic.coe_ofIntZpow, hx]
    have hmem : Dyadic.ofIntZpow z k ∈ F.unbounded :=
      F.mem_unbounded_of_mul_zpow_canonicalExp (by rw [hd]; exact hx.trans (two_zpow_shift z hk))
    rw [← hd] at h
    exact ⟨z, by rw [RoundsFinite.eq_of_mem hmem h, hd, hx]⟩
end RoundsFinite
end Mpfx
