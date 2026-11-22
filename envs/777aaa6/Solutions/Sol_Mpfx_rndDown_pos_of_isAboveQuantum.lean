-- Prove2me | solution 1 for Mpfx.rndDown_pos_of_isAboveQuantum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:47:37.182949+00:00
-- url     : https://prove2.me/submissions/2062c96f-719e-454b-b970-19bf5f05b7fb

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_zpow_log_le_rndDown

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hq : F.IsAboveQuantum x) : 0 < ((rndDown F x : Dyadic) : ℝ) :=
  lt_of_lt_of_le (zpow_pos (by norm_num) _) (zpow_log_le_rndDown F hx hq)
end Mpfx
