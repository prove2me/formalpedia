-- Prove2me | solution 1 for Mpfx.FiniteFormat.canonicalExp_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:53:52.532498+00:00
-- url     : https://prove2.me/submissions/a6dac454-e8a7-4f4e-b171-a3d78fb7cd28

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_le_iff
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_log_sub_p_le_canonicalExp

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0)
    (hyz : |y| ≤ |z|) : F.canonicalExp y ≤ F.canonicalExp z := by
  have hy_pos : 0 < |y| := abs_pos.mpr hy
  have hz : z ≠ 0 := by
    rintro rfl; rw [abs_zero] at hyz; exact absurd hyz (not_le.mpr hy_pos)
  have hlog : Int.log 2 |y| ≤ Int.log 2 |z| := Int.log_mono_right hy_pos hyz
  refine (F.canonicalExp_le_iff hy).mpr ⟨fun p hp => ?_, fun e he => F.exp_le_canonicalExp z he⟩
  have := F.log_sub_p_le_canonicalExp hz hp
  omega
end Mpfx.FiniteFormat
