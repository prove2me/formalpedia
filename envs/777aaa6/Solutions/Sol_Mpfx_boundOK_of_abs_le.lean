-- Prove2me | solution 1 for Mpfx.boundOK_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:30.8275+00:00
-- url     : https://prove2.me/submissions/33049216-d62c-4772-b3ad-270a84524071

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {b : Bound} {g h : Dyadic}
    (hle : |(g : ℝ)| ≤ |(h : ℝ)|) (hb : Format.boundOK b h) :
    Format.boundOK b g := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    have hle' : |(g : ℚ)| ≤ |(h : ℚ)| := by
      exact_mod_cast hle
    have hb' : |(h : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb
    change |(g : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
    linarith
end Mpfx
