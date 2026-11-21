-- Prove2me | solution 1 for Mpfx.FiniteFormat.mem_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:38:27.14009+00:00
-- url     : https://prove2.me/submissions/edeb62e1-7bcf-41be-8c68-1395237d8d10

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Format_mem_neg_iff

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (d : Dyadic) : (-d) ∈ F ↔ d ∈ F :=
  Format.mem_neg_iff F.toFormat d
end Mpfx.FiniteFormat
