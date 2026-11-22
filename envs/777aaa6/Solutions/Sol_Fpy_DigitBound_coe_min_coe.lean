-- Prove2me | solution 1 for Fpy.DigitBound.coe_min_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:52.022822+00:00
-- url     : https://prove2.me/submissions/a961207b-b115-4586-9a19-9598c27af5e5

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (a b : ℤ) : min (a : EInt) (b : EInt) = ((min a b : ℤ) : EInt) :=
  (WithBotTop.coe_monotone.map_min).symm
end Fpy.DigitBound
