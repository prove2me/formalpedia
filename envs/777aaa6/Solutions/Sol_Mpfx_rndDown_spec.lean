-- Prove2me | solution 1 for Mpfx.rndDown_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:03:12.468687+00:00
-- url     : https://prove2.me/submissions/531cb726-6fe5-493a-8b77-29a530cd9e68

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toNegative x (rndDown F x) :=
  RoundsFinite.toNegative_floor F x
end Mpfx
