-- Prove2me | solution 1 for Fpy.DigitBound.coe_add_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:16:16.047251+00:00
-- url     : https://prove2.me/submissions/ab23a3be-77fb-439e-a7c7-6513df722b6f

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (a b : ℤ) : ((a : EInt) + (b : EInt)) = ((a + b : ℤ) : EInt) := by
  change ((a : WithTop ℤ) : WithBot (WithTop ℤ)) + ((b : WithTop ℤ) : WithBot (WithTop ℤ)) =
    (((a + b : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  rw [← WithBot.coe_add, ← WithTop.coe_add]
end Fpy.DigitBound
