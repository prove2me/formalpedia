-- Prove2me | solution 1 for Mpfx.Format.boundOK_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:29:53.087609+00:00
-- url     : https://prove2.me/submissions/d57ef631-5a6a-4ae5-a625-2012f12f8b5d

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {b : Bound} {d : Dyadic} (h : boundOK b d) :
    boundOK b (-d) := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    change |((-d : Dyadic) : ℚ)| ≤ _
    rw [Subring.coe_neg, abs_neg]
    exact h
end Mpfx.Format
