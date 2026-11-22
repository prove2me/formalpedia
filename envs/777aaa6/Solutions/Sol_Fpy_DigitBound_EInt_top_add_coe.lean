-- Prove2me | solution 1 for Fpy.DigitBound.EInt.top_add_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:19.168383+00:00
-- url     : https://prove2.me/submissions/babecdf7-1027-4ff8-9e6e-77016bb6428e

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace EInt
theorem _root_.solution (k : ℤ) : (⊤ : EInt) + k = ⊤ := rfl
end EInt
end Fpy.DigitBound
