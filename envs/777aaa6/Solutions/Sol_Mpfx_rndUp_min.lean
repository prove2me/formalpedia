-- Prove2me | solution 1 for Mpfx.rndUp_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:12:29.321575+00:00
-- url     : https://prove2.me/submissions/2732659f-b63c-4496-ad08-9a0f1f588ccc

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndUp_spec

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz : z ∈ F.unbounded) (hxz : x ≤ (z : ℝ)) : (rndUp F x : ℝ) ≤ (z : ℝ) :=
  (rndUp_spec F x).2.2 z hz hxz
end Mpfx
