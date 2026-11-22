-- Prove2me | solution 1 for Mpfx.ulp_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:10:47.430522+00:00
-- url     : https://prove2.me/submissions/55a4a0ef-fa08-40f8-b3c7-0d162160a43c

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_ulp_of_ne_zero

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) : 0 < ulp F x := by
  rw [ulp_of_ne_zero F hx]; exact zpow_pos (by norm_num) _
end Mpfx
