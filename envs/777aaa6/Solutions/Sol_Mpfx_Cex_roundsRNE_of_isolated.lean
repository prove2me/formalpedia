-- Prove2me | solution 1 for Mpfx.Cex.roundsRNE_of_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:49.839173+00:00
-- url     : https://prove2.me/submissions/216e7e3e-fc7b-4666-8f91-be07526d35c7

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Theorems.Thm_Mpfx_Cex_Isolated_le_abs_sub
import Theorems.Thm_Mpfx_Cex_roundsDown_of_isolated
import Theorems.Thm_Mpfx_Cex_roundsUp_of_isolated

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : |x - h| < (2 : ℝ) ^ K / 2) :
    RoundsFinite F.unbounded (.nearest .toEven) x h := by
  -- Every other value is strictly farther from `x` than `h` is.
  have hfar : ∀ v ∈ F.unbounded, v ≠ h → |x - h| < |x - v| := fun v hv hne => by
    have h₁ := hK.le_abs_sub hv hne
    have h₂ := abs_sub_le (v : ℝ) x h
    rw [abs_sub_comm (v : ℝ) x] at h₂
    linarith
  have hfy : IsFaithfulRound F.unbounded x h := by
    have hx' := abs_lt.mp hx
    have h2K : (0 : ℝ) < 2 ^ K := zpow_pos two_pos K
    rcases le_total (h : ℝ) x with hhx | hxh
    · exact Or.inl (roundsDown_of_isolated hK hh hhx (by linarith))
    · exact Or.inr (roundsUp_of_isolated hK hh (by linarith) hxh)
  refine ⟨hh, hfy, fun v hv _ => ?_, fun ⟨v, hv, _, hne, heq⟩ => ?_⟩
  · by_cases hne : v = h
    · rw [hne]
    · exact (hfar v hv hne).le
  · exact absurd heq (hfar v hv hne).ne
end Mpfx.Cex
