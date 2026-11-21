-- Prove2me | solution 1 for Mpfx.FiniteFormat.neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:36.352977+00:00
-- url     : https://prove2.me/submissions/1956095f-b3e8-463a-97ab-701773c9fdf6

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Format_neg_mem

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution {F : FiniteFormat} {d : Dyadic} (h : d ∈ F) : (-d) ∈ F :=
  Format.neg_mem (F := F.toFormat) h
end Mpfx.FiniteFormat
