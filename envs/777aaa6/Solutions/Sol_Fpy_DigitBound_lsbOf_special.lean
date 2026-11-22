-- Prove2me | solution 1 for Fpy.DigitBound.lsbOf_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:25:33.944519+00:00
-- url     : https://prove2.me/submissions/5ed5824f-7a6d-48e3-b07a-09cc16b8a15b

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (s : Special) : lsbOf (.special s) = ⊤ := rfl
end Fpy.DigitBound
