-- Prove2me | solution 1 for Fpy.DigitBound.EInt.add_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:20:09.948847+00:00
-- url     : https://prove2.me/submissions/65ddf190-dfe0-4e73-8f7a-f419e1217938

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Fpy_DigitBound_EInt_top_add

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace EInt
theorem _root_.solution {a : EInt} (h : a ≠ ⊥) : a + ⊤ = ⊤ := by
  rw [add_comm]; exact EInt.top_add h
end EInt
end Fpy.DigitBound
