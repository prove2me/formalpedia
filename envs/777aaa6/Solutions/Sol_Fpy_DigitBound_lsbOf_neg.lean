-- Prove2me | solution 1 for Fpy.DigitBound.lsbOf_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:32:43.976787+00:00
-- url     : https://prove2.me/submissions/79ad8adc-ea05-411e-8afb-827932d92296

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg_real
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (u : Num) : lsbOf (Num.neg u) = lsbOf u := by
  rcases u with x | _
  · exact lsbOf_neg_real x
  · rfl
end Fpy.DigitBound
