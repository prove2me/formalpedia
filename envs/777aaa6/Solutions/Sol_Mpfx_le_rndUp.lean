-- Prove2me | solution 1 for Mpfx.le_rndUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:12:29.869442+00:00
-- url     : https://prove2.me/submissions/3fb05b79-1577-4568-b544-c64126c136b2

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndUp_spec

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) : x ≤ (rndUp F x : ℝ) :=
  (rndUp_spec F x).2.1
end Mpfx
