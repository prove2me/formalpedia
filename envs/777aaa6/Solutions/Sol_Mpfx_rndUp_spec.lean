-- Prove2me | solution 1 for Mpfx.rndUp_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:11:31.794224+00:00
-- url     : https://prove2.me/submissions/14f65e36-3ed8-4e96-9531-89fb8b81ab0f

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toPositive x (rndUp F x) :=
  RoundsFinite.toPositive_ceil F x
end Mpfx
