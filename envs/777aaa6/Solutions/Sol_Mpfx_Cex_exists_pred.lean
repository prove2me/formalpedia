-- Prove2me | solution 1 for Mpfx.Cex.exists_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:27.241772+00:00
-- url     : https://prove2.me/submissions/23924bf7-e01c-4eef-b495-16c8fa0e9178

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Theorems.Thm_Mpfx_Cex_exists_isolated_le
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_nonneg
import Theorems.Thm_Mpfx_rndDown_le
import Theorems.Thm_Mpfx_rndDown_max
import Theorems.Thm_Mpfx_rndDown_mem
import Theorems.Thm_Mpfx_rndDown_spec


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F : FiniteFormat) {a : Dyadic} (ha : a ∈ F.unbounded)
    (ha_pos : (0 : ℝ) < a) : ∃ u : Dyadic, Adjacent F u a ∧ 0 ≤ (u : ℝ) := by
  obtain ⟨K, hK, hK_le⟩ := exists_isolated_le F ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  set x₀ : ℝ := (a : ℝ) - (2 : ℝ) ^ K / 2 with hx₀
  refine ⟨rndDown F x₀, ⟨rndDown_mem F x₀, ha, (rndDown_le F x₀).trans_lt (by linarith),
    fun v hv hva => rndDown_max F x₀ hv (not_lt.mp fun hgt => ?_)⟩,
    RoundsFinite.toNegative_nonneg (by linarith) (rndDown_spec F x₀)⟩
  have := hK v hv (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
  rw [this] at hva
  exact lt_irrefl _ hva
end Mpfx.Cex
