-- Prove2me | solution 1 for Mpfx.rndUp_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:14:29.786102+00:00
-- url     : https://prove2.me/submissions/9fcf911d-04c5-412c-b732-a842b9f0160e

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndUp_spec

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) : rndUp F x ∈ F.unbounded :=
  (rndUp_spec F x).1
end Mpfx
