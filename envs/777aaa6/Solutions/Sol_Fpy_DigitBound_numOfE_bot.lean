-- Prove2me | solution 1 for Fpy.DigitBound.numOfE_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:16:54.312054+00:00
-- url     : https://prove2.me/submissions/2d892957-83d9-4de0-aba1-ea3bd2972768

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution : numOfE ⊥ = .special (.inf true) := rfl
end Fpy.DigitBound
