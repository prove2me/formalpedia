-- Prove2me | solution 1 for Mpfx.rndDown_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:51.282109+00:00
-- url     : https://prove2.me/submissions/4ecebae3-10ed-44ae-9b7f-c42b970734e6

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_spec
import Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) : rndDown F 0 = 0 :=
  RoundsFinite.eq_zero_of_zero (rndDown_spec F 0)
end Mpfx
