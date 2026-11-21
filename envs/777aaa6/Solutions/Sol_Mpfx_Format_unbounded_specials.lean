-- Prove2me | solution 1 for Mpfx.Format.unbounded_specials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:40.440268+00:00
-- url     : https://prove2.me/submissions/21c0e9b3-8f8f-4a24-8699-2025a160a89a

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) : F.unbounded.specials = F.specials := rfl
end Mpfx.Format
