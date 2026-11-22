-- Prove2me | solution 1 for Fpy.DigitBound.msbOf_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:18:40.768841+00:00
-- url     : https://prove2.me/submissions/10e77a76-45a0-48b5-a67f-a8886b001418

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (s : Special) : msbOf (.special s) = ⊤ := rfl
end Fpy.DigitBound
