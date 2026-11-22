-- Prove2me | solution 1 for Fpy.DigitBound.lsbOf_abs_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:48.61099+00:00
-- url     : https://prove2.me/submissions/bed5ef38-ebb5-4b46-aace-4c13793dde42

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg_real

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (x : ℝ) : lsbOf (.finite |x|) = lsbOf (.finite x) := by
  rcases abs_choice x with h | h <;> rw [h]; exact lsbOf_neg_real x
end Fpy.DigitBound
