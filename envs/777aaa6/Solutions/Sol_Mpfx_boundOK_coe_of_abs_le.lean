-- Prove2me | solution 1 for Mpfx.boundOK_coe_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:26:48.963291+00:00
-- url     : https://prove2.me/submissions/4f4064bc-ace6-45e6-a7f4-0509acea3391

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {b : NonNegDyadic} {y : Dyadic}
    (h : |(y : ℝ)| ≤ ((b.val : Dyadic) : ℝ)) :
    Format.boundOK ((b : Bound)) y := by
  change |(y : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
  exact_mod_cast h
end Mpfx
