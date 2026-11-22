-- Prove2me | solution 1 for Fpy.DigitBound.numOfE_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:16:25.211627+00:00
-- url     : https://prove2.me/submissions/a61d43b2-aea0-416c-be53-f515db7ab5dc

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (k : ℤ) : numOfE k = .finite (k : ℝ) := rfl
end Fpy.DigitBound
