-- Prove2me | solution 1 for Fpy.DigitBound.lsb_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:31:25.094384+00:00
-- url     : https://prove2.me/submissions/3cff5007-cf0d-426a-9627-d392ebc9b394

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Fpy_DigitBound_EInt_le_of_forall_coe_le
import Theorems.Thm_Fpy_DigitBound_coe_le_lsbOf
import Theorems.Thm_Fpy_Num_add_eq_finite


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (u v : Num) : min (lsbOf u) (lsbOf v) ≤ lsbOf (Num.add u v) := by
  cases h : Num.add u v with
  | special => exact le_top
  | finite =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := Num.add_eq_finite h
    refine EInt.le_of_forall_coe_le fun k hk => ?_
    obtain ⟨a, ha⟩ := coe_le_lsbOf.mp (hk.trans (min_le_left _ _))
    obtain ⟨b, hb⟩ := coe_le_lsbOf.mp (hk.trans (min_le_right _ _))
    exact coe_le_lsbOf.mpr ⟨a + b, by rw [ha, hb]; push_cast; ring⟩
end Fpy.DigitBound
