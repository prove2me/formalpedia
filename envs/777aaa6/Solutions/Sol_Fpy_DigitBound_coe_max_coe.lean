-- Prove2me | solution 1 for Fpy.DigitBound.coe_max_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:20:43.209016+00:00
-- url     : https://prove2.me/submissions/4bd08518-22bf-4faa-adb2-85ddafa6eb27

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (a b : ℤ) : max (a : EInt) (b : EInt) = ((max a b : ℤ) : EInt) :=
  (WithBotTop.coe_monotone.map_max).symm
end Fpy.DigitBound
