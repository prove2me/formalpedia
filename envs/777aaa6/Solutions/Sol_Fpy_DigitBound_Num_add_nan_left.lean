-- Prove2me | solution 1 for Fpy.DigitBound.Num.add_nan_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:44:38.904327+00:00
-- url     : https://prove2.me/submissions/154f8f87-e42e-4aa4-a378-636aba33f8c1

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace Num
theorem _root_.solution (w : Num) : Num.add nan w = nan := by
  rcases w with _ | (_ | _) <;> rfl
end Num
end Fpy.DigitBound
