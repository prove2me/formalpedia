-- Prove2me | solution 1 for Fpy.DigitBound.lsbOf_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:36:18.975624+00:00
-- url     : https://prove2.me/submissions/d6ad0469-b969-4b5d-8c7f-ef2fa3bdc721

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Fpy_DigitBound_lsbOf_abs_real

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (u : Num) : lsbOf (Num.abs u) = lsbOf u := by
  rcases u with x | (_ | _)
  · exact lsbOf_abs_real x
  all_goals rfl
end Fpy.DigitBound
