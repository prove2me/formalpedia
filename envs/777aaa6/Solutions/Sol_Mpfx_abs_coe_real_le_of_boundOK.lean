-- Prove2me | solution 1 for Mpfx.abs_coe_real_le_of_boundOK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:52.234382+00:00
-- url     : https://prove2.me/submissions/d8cfe055-7a94-483e-ab96-67d53e1195e7

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {b₁ : NonNegDyadic} {y : Dyadic}
    (h : Format.boundOK ((b₁ : Bound)) y) :
    |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
  exact_mod_cast h
end Mpfx
