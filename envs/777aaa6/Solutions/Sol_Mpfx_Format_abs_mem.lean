-- Prove2me | solution 1 for Mpfx.Format.abs_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:53.843192+00:00
-- url     : https://prove2.me/submissions/e7717150-61b9-457a-967d-d47e002b3196

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Format_neg_mem

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} {x : Dyadic} (hx : x ∈ F) :
    Dyadic.abs x ∈ F := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℚ)
  · rw [if_pos h]; exact hx
  · rw [if_neg h]; exact neg_mem hx
end Mpfx.Format
