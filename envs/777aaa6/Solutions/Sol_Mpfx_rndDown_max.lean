-- Prove2me | solution 1 for Mpfx.rndDown_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:05:15.920221+00:00
-- url     : https://prove2.me/submissions/fd424ea5-f9e5-42f0-946b-ae77170be251

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_spec

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz : z ∈ F.unbounded) (hzx : (z : ℝ) ≤ x) : (z : ℝ) ≤ (rndDown F x : ℝ) :=
  (rndDown_spec F x).2.2 z hz hzx
end Mpfx
