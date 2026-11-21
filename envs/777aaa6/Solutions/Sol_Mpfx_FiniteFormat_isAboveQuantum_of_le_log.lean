-- Prove2me | solution 1 for Mpfx.FiniteFormat.isAboveQuantum_of_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:26.151691+00:00
-- url     : https://prove2.me/submissions/93c3df94-e449-4777-9845-c4b8a9caec08

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution {F : FiniteFormat} {x : ℝ} (hx : 0 < x)
    (h : F.canonicalExp x ≤ Int.log 2 x) : F.IsAboveQuantum x := by
  have : Int.log 2 |x| = Int.log 2 x := by rw [abs_of_pos hx]
  omega
end Mpfx.FiniteFormat
