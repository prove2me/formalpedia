-- Prove2me | solution 1 for Mpfx.FiniteFormat.IsAboveQuantum.le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:24.469352+00:00
-- url     : https://prove2.me/submissions/cdc0d214-3f93-4207-9bfd-559e27d73037

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
namespace IsAboveQuantum
theorem _root_.solution {F : FiniteFormat} {x : ℝ} (h : F.IsAboveQuantum x)
    (hx : 0 < x) : F.canonicalExp x ≤ Int.log 2 x := by
  have h' : F.canonicalExp x ≤ Int.log 2 |x| := h
  rwa [abs_of_pos hx] at h'
end IsAboveQuantum
end Mpfx.FiniteFormat
