-- Prove2me | solution 1 for Fpy.DigitBound.msbOf_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:23:03.706735+00:00
-- url     : https://prove2.me/submissions/b4f19150-1959-4b2a-a36b-733b18978d66

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Fpy_DigitBound_EInt_le_of_forall_le_coe
import Theorems.Thm_Fpy_DigitBound_msbOf_le_coe

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {x y : ℝ} (h : |x| ≤ |y|) : msbOf (.finite x) ≤ msbOf (.finite y) :=
  EInt.le_of_forall_le_coe fun _ hk => msbOf_le_coe.mpr (h.trans_lt (msbOf_le_coe.mp hk))
end Fpy.DigitBound
