-- Prove2me | solution 1 for Mpfx.rndUp_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:51.741329+00:00
-- url     : https://prove2.me/submissions/645627ba-b903-4640-b74f-bfa57e5be29f

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndUp_spec
import Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) : rndUp F 0 = 0 :=
  RoundsFinite.eq_zero_of_zero (rndUp_spec F 0)
end Mpfx
