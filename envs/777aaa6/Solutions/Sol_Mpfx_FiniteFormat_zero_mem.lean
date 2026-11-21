-- Prove2me | solution 1 for Mpfx.FiniteFormat.zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:38:28.875672+00:00
-- url     : https://prove2.me/submissions/10dcba4e-981a-48a1-b278-a60c4a6aea11

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Format_zero_mem

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) : (0 : Dyadic) ∈ F := Format.zero_mem F.toFormat
end Mpfx.FiniteFormat
