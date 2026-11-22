-- Prove2me | solution 1 for Fpy.DigitBound.Num.add_nan_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:45:00.309168+00:00
-- url     : https://prove2.me/submissions/7fc3310d-8eb1-4c7a-ab11-cf85759dbb13

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace Num
theorem _root_.solution (s : Num) : Num.add s nan = nan := by
  rcases s with _ | (_ | _) <;> rfl
end Num
end Fpy.DigitBound
