-- Prove2me | solution 1 for Mpfx.nearest_error_le_half_ulp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:24:07.45835+00:00
-- url     : https://prove2.me/submissions/5bde1496-b9f3-4254-80f7-0252e682c98d

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_spec
import Theorems.Thm_Mpfx_rndDown_le
import Theorems.Thm_Mpfx_rndDown_mem
import Theorems.Thm_Mpfx_rndUp_spec
import Theorems.Thm_Mpfx_le_rndUp
import Theorems.Thm_Mpfx_rndUp_mem
import Theorems.Thm_Mpfx_rndUp_le_rndDown_add_ulp
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_RoundsFinite_nearest_min


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {z : Dyadic} (h : RoundsFinite F.unbounded (.nearest tb) x z) :
    |(z : ℝ) - x| ≤ ulp F x / 2 := by
  have h1 : |x - (z : ℝ)| ≤ |x - (rndDown F x : ℝ)| :=
    h.nearest_min (rndDown_mem F x) (rndDown_spec F x).isFaithfulRound
  have h2 : |x - (z : ℝ)| ≤ |x - (rndUp F x : ℝ)| :=
    h.nearest_min (rndUp_mem F x) (rndUp_spec F x).isFaithfulRound
  have hax : (rndDown F x : ℝ) ≤ x := rndDown_le F x
  have hxa' : x ≤ (rndUp F x : ℝ) := le_rndUp F x
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - (rndDown F x : ℝ))] at h1
  rw [abs_of_nonpos (by linarith : x - (rndUp F x : ℝ) ≤ 0), neg_sub] at h2
  have hulp : (rndUp F x : ℝ) - (rndDown F x : ℝ) ≤ ulp F x := by
    have := rndUp_le_rndDown_add_ulp F x; linarith
  rw [abs_sub_comm]
  linarith
end Mpfx
