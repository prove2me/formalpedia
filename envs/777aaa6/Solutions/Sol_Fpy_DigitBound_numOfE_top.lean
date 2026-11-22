-- Prove2me | solution 1 for Fpy.DigitBound.numOfE_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:16:44.086502+00:00
-- url     : https://prove2.me/submissions/75ed5fdd-f575-485e-80c0-dc1b3b40ae92

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution : numOfE ⊤ = .special (.inf false) := rfl
end Fpy.DigitBound
